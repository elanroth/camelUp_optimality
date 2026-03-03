-- CamelUp.Controller.EV
-- Per-move expected-value evaluation via Monte Carlo simulation.
--
-- Design:
--   • For Roll moves: the player doesn't choose the die outcome — a random
--     camel die is drawn uniformly from the bag and rolled 1-3 uniformly.
--     EV(Roll) = average over all 15 equally-likely die outcomes of
--                [1 coin (pyramid) + EV(resulting state)].
--     We compute this by iterating over legalDieOutcomes and averaging
--     N/|outcomes| simulations per outcome (or N total via sampling).
--   • For BetLeg / BetRaceWin / BetRaceLose: deterministic move application,
--     then N full-race simulations from the resulting state.
--   • "EV" = expected final score for the current player minus their
--     current score, i.e. the expected *gain* from choosing this move.
--
-- Rollout policy in simulation: pure Roll (no additional bet moves).
-- This is the standard first-order MC approximation; M6 adds bot policies.
import CamelUp.Model.Types
import CamelUp.Model.Step
import CamelUp.Controller.Sim

namespace CamelUp.EV

open CamelUp CamelUp.Sim

/-! ## Helpers -/

/-- Convert Int to Float (Lean 4.28 lacks Int.toFloat). -/
private def intToFloat (n : Int) : Float :=
  if n >= 0 then n.toNat.toFloat
  else -((-n).toNat.toFloat)

/-- Simulate `n` full races from `gs` using random die rolls only.
    Returns the mean final score for player `player`. -/
def evalState (gs : GameState) (player : Nat) (rng : RNG) (n : Nat)
    : Float × RNG :=
  let (total, rng') :=
    (List.range n).foldl (fun (acc : Float × RNG) _ =>
      let (sum, rng) := acc
      let (gs', _, rng') := simulateRace gs rng
      let finalScore : Float := intToFloat (gs'.scores.getD player 0)
      (sum + finalScore, rng'))
    (0.0, rng)
  let mean := if n = 0 then 0.0 else total / n.toFloat
  (mean, rng')

/-! ## Per-move EV -/

/-- A single evaluated move. -/
structure MoveEval where
  /-- Human-readable label; Roll bundles all die outcomes into one entry. -/
  label       : String
  /-- The representative move (for Roll: arbitrary outcome, not used for apply). -/
  move        : Move
  /-- Expected final score for the current player after this move + optimal play. -/
  meanScore   : Float
  /-- Expected *gain*: meanScore minus current score baseline. -/
  ev          : Float
  deriving Repr

instance : ToString MoveEval where
  toString me :=
    let evSign := if me.ev >= 0.0 then "+" else ""
    let pad    := if me.label.length < 22
                  then String.mk (List.replicate (22 - me.label.length) ' ')
                  else ""
    s!"{me.label}{pad} EV={evSign}{me.ev}"

/-! ## Evaluation for each move class -/

/-- Evaluate a deterministic (non-Roll) move: apply it, then simulate `n` races. -/
def evalDetMove (gs : GameState) (move : Move) (baseline : Float)
    (rng : RNG) (n : Nat) : MoveEval × RNG :=
  match step gs move with
  | none     =>
      -- Illegal move — return large negative sentinel so it sorts last
      ({ label := toString move, move, meanScore := -999.0, ev := -999.0 }, rng)
  | some gs' =>
      let (mean, rng') := evalState gs' gs.currentPlayer rng n
      ({ label     := toString move
         move      := move
         meanScore := mean
         ev        := mean - baseline }, rng')

/-- Evaluate the Roll action.
    EV(Roll) = mean over all |outcomes| die outcomes of
               meanScore(state after that die outcome).
    We use `n` total simulations split evenly across outcomes; any remainder
    goes to the first outcome.  Requires outcomes.length > 0. -/
def evalRollAction (gs : GameState) (baseline : Float) (rng : RNG) (n : Nat)
    : MoveEval × RNG :=
  let outcomes := legalDieOutcomes gs
  if outcomes.isEmpty then
    ({ label := "Roll", move := Move.Roll { camel := .White, value := 0 },
       meanScore := baseline, ev := 0.0 }, rng)
  else
    -- Distribute n sims evenly across all outcomes.
    let perOutcome := max 1 (n / outcomes.length)
    let (total, rng') :=
      outcomes.foldl (fun (acc : Float × RNG) outcome =>
        let (sum, rng) := acc
        match step gs (Move.Roll outcome) with
        | none     => (sum, rng)   -- shouldn't happen for legal outcomes
        | some gs' =>
            let (mean, rng') := evalState gs' gs.currentPlayer rng perOutcome
            (sum + mean, rng'))
      (0.0, rng)
    let meanScore := total / outcomes.length.toFloat
    let rep := Move.Roll (outcomes.head?.getD { camel := .White, value := 0 })
    ({ label     := "Roll"
       move      := rep
       meanScore := meanScore
       ev        := meanScore - baseline }, rng')

/-! ## Move ranker -/

/-- Evaluate all legal move *types* from `gs` and return them ranked
    highest-EV first.

    `simsPerMove` = number of MC race simulations per deterministic move
                   (Roll always uses simsPerMove total, split across outcomes). -/
def rankMoves (gs : GameState) (seed : UInt64) (simsPerMove : Nat)
    : List MoveEval :=
  if gs.gameOver then []
  else
    let rng0 : RNG := { seed }
    -- Compute baseline: expected score if we do nothing (not quite right, but
    -- provides a delta reference; we set it from pure evalState on gs itself).
    let (baseline, rng1) := evalState gs gs.currentPlayer rng0 simsPerMove

    -- 1. Roll action (one combined entry)
    let (rollEval, rng2) := evalRollAction gs baseline rng1 simsPerMove

    -- 2. BetLeg moves (one per camel that still has tiles)
    let (legEvals, rng3) :=
      CamelColor.all.foldl (fun (acc : List MoveEval × RNG) c =>
        let (evals, rng) := acc
        if (gs.legBetTiles.getD (CamelColor.toIdx c) []).isEmpty then (evals, rng)
        else
          let m := Move.BetLeg c
          let (me, rng') := evalDetMove gs m baseline rng simsPerMove
          (evals ++ [me], rng'))
      ([], rng2)

    -- 3. BetRaceWin moves (one per camel)
    let (winEvals, rng4) :=
      CamelColor.all.foldl (fun (acc : List MoveEval × RNG) c =>
        let (evals, rng) := acc
        let m := Move.BetRaceWin c
        let (me, rng') := evalDetMove gs m baseline rng simsPerMove
        (evals ++ [me], rng'))
      ([], rng3)

    -- 4. BetRaceLose moves (one per camel)
    let (loseEvals, _) :=
      CamelColor.all.foldl (fun (acc : List MoveEval × RNG) c =>
        let (evals, rng) := acc
        let m := Move.BetRaceLose c
        let (me, rng') := evalDetMove gs m baseline rng simsPerMove
        (evals ++ [me], rng'))
      ([], rng4)

    let all := [rollEval] ++ legEvals ++ winEvals ++ loseEvals
    -- Sort descending by EV (insertion sort — list is small ≤ 21 entries).
    let insertSorted (me : MoveEval) (sorted : List MoveEval) : List MoveEval :=
      let rec ins : List MoveEval → List MoveEval
        | []        => [me]
        | x :: rest => if me.ev >= x.ev then me :: x :: rest else x :: ins rest
      ins sorted
    all.foldl (fun sorted me => insertSorted me sorted) []

end CamelUp.EV
