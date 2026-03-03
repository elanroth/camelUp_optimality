-- CamelUp.Controller.Sim
-- Monte Carlo simulation engine.  This module is the only place that touches
-- randomness; the Model is kept fully pure.
--
-- Architecture (MVC):
--   Model      : CamelUp.Model.*        pure rules, no IO, no RNG
--   Controller : this file             orchestrates simulations, queries Model
--   View       : CamelUp.View.*        renders results as strings
import CamelUp.Model.Types
import CamelUp.Model.Step

namespace CamelUp.Sim

/-! ## Deterministic RNG -/

/-- Minimal linear-congruential generator.  Deterministic given a seed;
    kept outside IO so all callers are pure. -/
structure RNG where
  seed : UInt64
  deriving Repr

/-- Advance the generator one step; return new state and a raw value. -/
def RNG.next (r : RNG) : RNG × UInt64 :=
  let s := r.seed * 6364136223846793005 + 1442695040888963407
  ({ seed := s }, s)

-- Safe list indexing (List.get? absent in Lean 4.28).
private def listGet? {α : Type} : List α → Nat → Option α
  | [],     _     => none
  | x :: _, 0     => some x
  | _ :: t, i + 1 => listGet? t i

/-- Pick a uniformly random element from a non-empty list. -/
def RNG.pick {α : Type} (r : RNG) (xs : List α) : RNG × Option α :=
  if xs.isEmpty then (r, none)
  else
    let (r', v) := r.next
    let len : UInt64 := UInt64.ofNat xs.length
    let idx : Nat    := (v % len).toNat
    (r', listGet? xs idx)

/-! ## Outcome accumulator -/

/-- Tally of how many times each camel won a simulated leg or race. -/
abbrev WinCounts := List (CamelColor × Nat)

def WinCounts.empty : WinCounts := CamelColor.all.map (·, 0)

def WinCounts.record (wc : WinCounts) (c : CamelColor) : WinCounts :=
  wc.map (fun (color, n) => if color == c then (color, n + 1) else (color, n))

/-! ## Leg simulator (M3: uses Move.Roll; halts on gameOver too) -/

/-- Simulate one leg from `gs` to completion (bag exhausted or race over).
    Returns `(finalState, legLeader, newRNG)`. -/
def simulateLeg (gs : GameState) (rng : RNG) (maxSteps : Nat := 20)
    : GameState × Option CamelColor × RNG :=
  let startLeg := gs.legNo
  let rec go : GameState → RNG → Nat → GameState × Option CamelColor × RNG
    | gs, rng, 0        => (gs, gs.leader, rng)
    | gs, rng, fuel + 1 =>
        if gs.legNo > startLeg || gs.gameOver then (gs, gs.leader, rng)
        else
          let outcomes := legalDieOutcomes gs
          let (rng', mOutcome) := rng.pick outcomes
          match mOutcome with
          | none => (gs, gs.leader, rng')
          | some outcome =>
              match step gs (Move.Roll outcome) with
              | none     => (gs, gs.leader, rng')
              | some gs' => go gs' rng' fuel
  go gs rng maxSteps

/-! ## Race simulator (M3) -/

/-- Simulate an entire race from `gs` until `gameOver`, rolling dice randomly.
    Returns `(finalState, raceWinner, newRNG)`. -/
def simulateRace (gs : GameState) (rng : RNG) (maxSteps : Nat := 500)
    : GameState × Option CamelColor × RNG :=
  let rec go : GameState → RNG → Nat → GameState × Option CamelColor × RNG
    | gs, rng, 0        => (gs, gs.raceWinner, rng)
    | gs, rng, fuel + 1 =>
        if gs.gameOver then (gs, gs.raceWinner, rng)
        else
          let outcomes := legalDieOutcomes gs
          let (rng', mOutcome) := rng.pick outcomes
          match mOutcome with
          | none => (gs, gs.raceWinner, rng')
          | some outcome =>
              match step gs (Move.Roll outcome) with
              | none     => (gs, gs.raceWinner, rng')
              | some gs' => go gs' rng' fuel
  go gs rng maxSteps

/-! ## Probability estimation -/

/-- Run `n` leg simulations; return tally of leg-leader counts. -/
def estimateLegWinProbs (gs : GameState) (seed : UInt64) (n : Nat) : WinCounts :=
  let rng0 : RNG := { seed }
  (List.range n).foldl (fun (acc : RNG × WinCounts) _ =>
    let (rng, wc) := acc
    let (_, mLeader, rng') := simulateLeg gs rng
    let wc' := match mLeader with
      | none   => wc
      | some c => wc.record c
    (rng', wc'))
  (rng0, WinCounts.empty)
  |>.2

/-- Run `n` full-race simulations; return tally of race-winner counts. -/
def estimateRaceWinProbs (gs : GameState) (seed : UInt64) (n : Nat) : WinCounts :=
  let rng0 : RNG := { seed }
  (List.range n).foldl (fun (acc : RNG × WinCounts) _ =>
    let (rng, wc) := acc
    let (_, mWinner, rng') := simulateRace gs rng
    let wc' := match mWinner with
      | none   => wc
      | some c => wc.record c
    (rng', wc'))
  (rng0, WinCounts.empty)
  |>.2

end CamelUp.Sim
