-- CamelUp.Controller.VarSeek
-- Variance-seeking (risk-adaptive) controller.
--
-- Motivation:
--   mughBot maximises E[score] (linear utility).  That is optimal when scores
--   are tied.  When a player is *behind*, high-variance moves are actually
--   better: you need a lucky break, so convex utility (rewards big upside)
--   is the right shape.  When *ahead*, concave utility locks the lead.
--
-- Key exports:
--   varSeekBot  — policy that adapts utility shape to the score situation
import CamelUp.Model.Types
import CamelUp.Model.Step
import CamelUp.Controller.Sim
import CamelUp.Controller.EV
import CamelUp.Controller.Policy

namespace CamelUp.VarSeek

open CamelUp CamelUp.Sim CamelUp.EV CamelUp.Policy

-- ─── Float helper (local to avoid dependency on EV internals) ────────────────

private def vsFloat (i : Int) : Float :=
  if i >= 0 then (i.toNat : Nat).toFloat
  else -((-i).toNat : Nat).toFloat

-- ─── Deficit detection ───────────────────────────────────────────────────────

/-- How far `player` is behind the current leader (positive = losing). -/
def playerDeficit (gs : GameState) (player : Nat) : Int :=
  let myScore   := gs.scores.getD player 0
  let bigNeg    := (0 : Int) - 9999
  let bestOther := (List.range gs.numPlayers).foldl (fun best p =>
    if p == player then best else max best (gs.scores.getD p 0)) bigNeg
  bestOther - myScore

-- ─── Utility shapes ──────────────────────────────────────────────────────────

/-- Linear — same as mughBot. -/
def linearUtility (score : Int) : Float := vsFloat score

/-- Convex (score² / 100): disproportionately rewards big wins.
    Use when trailing (need variance). -/
def convexUtility (score : Int) : Float :=
  let f := vsFloat score
  f * f / 100.0

/-- Concave (√|score| with sign): dampens marginal gains.
    Use when leading (protect the lead). -/
def concaveUtility (score : Int) : Float :=
  let f := vsFloat score
  if f >= 0.0 then Float.sqrt f else -(Float.sqrt (-f))

/-- Pick utility shape based on deficit vs ±3-coin threshold. -/
def adaptiveUtility (gs : GameState) (player : Nat) (score : Int) : Float :=
  let d := playerDeficit gs player
  if d >= 3       then convexUtility score
  else if d <= -3 then concaveUtility score
  else                  linearUtility score

-- ─── Utility-weighted simulator ──────────────────────────────────────────────

/-- Run `n` full-race simulations; return mean utility(finalScore[player]). -/
def evalStateU (utility : Int → Float) (gs : GameState) (player : Nat)
    (rng : RNG) (n : Nat) : Float × RNG :=
  let (total, rng') := (List.range n).foldl (fun (acc : Float × RNG) _ =>
    let (sum, r) := acc
    let (gs', _, r') := simulateRace gs r
    (sum + utility (gs'.scores.getD player 0), r')) (0.0, rng)
  let mean := if n == 0 then 0.0 else total / (n : Nat).toFloat
  (mean, rng')

private def evalDetU (utility : Int → Float) (gs : GameState) (player : Nat)
    (move : Move) (rng : RNG) (n : Nat) : Float × RNG :=
  match step gs move with
  | none     => (utility (gs.scores.getD player 0), rng)
  | some gs' => evalStateU utility gs' player rng n

private def evalRollU (utility : Int → Float) (gs : GameState) (player : Nat)
    (rng : RNG) (n : Nat) : Float × RNG :=
  let outcomes := legalDieOutcomes gs
  let k := outcomes.length
  if k == 0 then (utility (gs.scores.getD player 0), rng)
  else
    let perOut := n / k + 1
    let (total, rng') := outcomes.foldl (fun (acc : Float × RNG) o =>
      let (sum, r) := acc
      let (v, r') := evalDetU utility gs player (Move.Roll o) r perOut
      (sum + v, r')) (0.0, rng)
    (total / (k : Nat).toFloat, rng')

/-- Rank all legal moves by utility-weighted score (descending). -/
def rankMovesU (utility : Int → Float) (gs : GameState) (seed : UInt64)
    (simsPerMove : Nat) : List MoveEval :=
  let player   := gs.currentPlayer
  let rng0     : RNG := { seed }
  let baseline := utility (gs.scores.getD player 0)
  let (rollScore, rng1) := evalRollU utility gs player rng0 simsPerMove
  let rollME : MoveEval :=
    { label     := "Roll"
      move      := Move.Roll { camel := .White, value := 0 }
      meanScore := rollScore
      ev        := rollScore - baseline }
  let betMoves : List Move :=
    CamelColor.all.map Move.BetLeg ++
    CamelColor.all.map Move.BetRaceWin ++
    CamelColor.all.map Move.BetRaceLose
  let rec insertDesc : List MoveEval → MoveEval → List MoveEval
    | [],     x => [x]
    | h :: t, x => if x.meanScore >= h.meanScore then x :: h :: t
                   else h :: insertDesc t x
  let (meList, _) := betMoves.foldl (fun (acc : List MoveEval × RNG) m =>
    let (lst, r) := acc
    let (v, r') := evalDetU utility gs player m r simsPerMove
    let me : MoveEval :=
      { label := toString m, move := m
        meanScore := v, ev := v - baseline }
    (insertDesc lst me, r')) ([rollME], rng1)
  meList

-- ─── varSeekBot policy ───────────────────────────────────────────────────────

/-- Risk-adaptive bot: convex utility when behind ≥ 3, concave when ahead ≥ 3,
    linear (≡ mughBot) otherwise.  Delegates die rolls to randomPolicy. -/
def varSeekBot (simsPerMove : Nat := 300) : Policy := fun gs rng =>
  let player  := gs.currentPlayer
  let utility := adaptiveUtility gs player
  let ranked  := rankMovesU utility gs rng.seed simsPerMove
  let (rng', _) := rng.next
  match ranked.head? with
  | none    => randomPolicy gs rng'
  | some me =>
    match me.move with
    | Move.Roll _ => randomPolicy gs rng'
    | other       => (other, rng')

end CamelUp.VarSeek
