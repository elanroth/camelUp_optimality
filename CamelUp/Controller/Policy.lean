-- CamelUp.Controller.Policy
-- Named policies and head-to-head game simulation.
--
-- A Policy is a pure function: GameState → RNG → Move × RNG.
-- This keeps the Controller free of IO just like the Model and Sim.
--
-- Policies defined here:
--   randomPolicy  — picks a legal die outcome uniformly at random (always rolls)
--   mughBot       — picks the highest-EV move via rankMoves; falls back to Roll
--
-- Head-to-head simulation:
--   simulateGame runs one full game where each player i uses policies[i],
--   returning the final GameState (with scores).
--   runTournament runs N games and accumulates average scores per player.
import CamelUp.Model.Types
import CamelUp.Model.Step
import CamelUp.Controller.Sim
import CamelUp.Controller.EV

namespace CamelUp.Policy

open CamelUp CamelUp.Sim CamelUp.EV

-- Local helper: Int → Float (mirrors intToFloat from EV; needed here because
-- `open CamelUp.EV` may not bring private defs into scope in all kernels).
private def floatOfInt (i : Int) : Float :=
  if i ≥ 0 then (i.toNat : Nat).toFloat
  else -(((-i).toNat : Nat).toFloat)

-- Local helper: update one element of an Array.
private def arrSetF (a : Array Float) (i : Nat) (v : Float) : Array Float :=
  a.mapIdx (fun j x => if j == i then v else x)
private def arrSetN (a : Array Nat) (i : Nat) (v : Nat) : Array Nat :=
  a.mapIdx (fun j x => if j == i then v else x)

/-! ## Policy type -/

/-- A policy maps a game state + RNG to a chosen move and updated RNG.
    Must return a legal move (callers may fall back to Roll on illegality). -/
abbrev Policy := GameState → RNG → Move × RNG

/-! ## Built-in policies -/

/-- Always roll: pick a random legal die outcome uniformly. -/
def randomPolicy : Policy := fun gs rng =>
  let outcomes := legalDieOutcomes gs
  match outcomes with
  | [] =>
      -- No dice left (leg boundary): just return a dummy Roll; step handles it
      (Move.Roll { camel := .White, value := 0 }, rng)
  | _ =>
      let (rng', mOut) := rng.pick outcomes
      match mOut with
      | none    => (Move.Roll { camel := .White, value := 0 }, rng')
      | some o  => (Move.Roll o, rng')

/-- mughBot: choose the highest-EV move via Monte Carlo ranking.
    Uses `simsPerMove` rollouts per candidate move.
    Falls back to `randomPolicy` if ranking is empty (shouldn't happen). -/
def mughBot (simsPerMove : Nat := 300) : Policy := fun gs rng =>
  let ranked := rankMoves gs rng.seed simsPerMove
  -- Advance RNG so we don't reuse the same seed next call.
  let (rng', _) := rng.next
  match ranked.head? with
  | none    => randomPolicy gs rng'
  | some me =>
    match me.move with
    | Move.Roll _ =>
        -- For Roll, we must pick an actual die outcome randomly
        -- (mughBot decided Roll is best; now choose uniformly among outcomes).
        randomPolicy gs rng'
    | other => (other, rng')

/-! ## Game simulator -/

/-- Simulate one full game.
    `policies` is indexed by player number; players without an entry use randomPolicy.
    Returns final GameState (scores populated, gameOver = true). -/
def simulateGame (gs : GameState) (policies : Array Policy) (rng : RNG)
    (maxSteps : Nat := 2000) : GameState × RNG :=
  let getPolicy (p : Nat) : Policy :=
    policies.getD p randomPolicy
  let rec go : GameState → RNG → Nat → GameState × RNG
    | gs, rng, 0        => (gs, rng)
    | gs, rng, fuel + 1 =>
        if gs.gameOver then (gs, rng)
        else
          let p := gs.currentPlayer
          let policy := getPolicy p
          let (move, rng') := policy gs rng
          match step gs move with
          | none     =>
              -- Illegal move from policy: fall back to random roll
              let (move2, rng2) := randomPolicy gs rng'
              match step gs move2 with
              | none     => (gs, rng2)   -- shouldn't happen
              | some gs' => go gs' rng2 fuel
          | some gs' => go gs' rng' fuel
  go gs rng maxSteps

/-! ## Tournament runner -/

/-- Result of a tournament: mean score per player across N games. -/
structure TournamentResult where
  numGames   : Nat
  numPlayers : Nat
  totalScores : Array Float   -- sum of final scores; divide by numGames for mean
  deriving Repr

def TournamentResult.mean (r : TournamentResult) (p : Nat) : Float :=
  if r.numGames = 0 then 0.0
  else (r.totalScores.getD p 0.0) / r.numGames.toFloat

def TournamentResult.winRate (r : TournamentResult) (wins : Array Nat) (p : Nat) : Float :=
  if r.numGames = 0 then 0.0
  else (wins.getD p 0).toFloat / r.numGames.toFloat

/-- Run `n` full games from initial state `gs` with the given policy array.
    Returns (TournamentResult, win counts per player). -/
def runTournament (gs : GameState) (policies : Array Policy) (seed : UInt64) (n : Nat)
    : TournamentResult × Array Nat :=
  let nPlayers := gs.numPlayers
  let initScores : Array Float := (List.replicate nPlayers 0.0).toArray
  let initWins   : Array Nat   := (List.replicate nPlayers 0).toArray
  let rng0 : RNG := { seed }
  let (_, totals, wins) :=
    (List.range n).foldl (fun (acc : RNG × Array Float × Array Nat) _ =>
      let (rng, tots, wins) := acc
      let (finalGs, rng') := simulateGame gs policies rng
      -- accumulate scores
      let tots' := (List.range nPlayers).foldl (fun arr p =>
        let s : Float := floatOfInt (finalGs.scores.getD p 0)
        arrSetF arr p (arr.getD p 0.0 + s)) tots
      -- accumulate wins (highest score wins; ties go to lower player index)
      let bestScore := (List.range nPlayers).foldl (fun best p =>
        max best (finalGs.scores.getD p 0)) (Int.ofNat 0 - 9999)
      let wins' := (List.range nPlayers).foldl (fun arr p =>
        if finalGs.scores.getD p 0 == bestScore then
          arrSetN arr p (arr.getD p 0 + 1)
        else arr) wins
      (rng', tots', wins'))
    (rng0, initScores, initWins)
  ({ numGames := n, numPlayers := nPlayers, totalScores := totals }, wins)

/-! ## Pretty-printing helpers -/

def tournamentSummary (label : String) (result : TournamentResult)
    (wins : Array Nat) (policyNames : Array String) : String :=
  let header := s!"=== {label} ({result.numGames} games) ==="
  let lines := (List.range result.numPlayers).map (fun p =>
    let name    := policyNames.getD p s!"P{p}"
    let mean    := result.mean p
    let wr      := result.winRate wins p * 100.0
    s!"  {name}: mean score = {mean}  win rate = {wr}%")
  String.intercalate "\n" ([header] ++ lines)

end CamelUp.Policy
