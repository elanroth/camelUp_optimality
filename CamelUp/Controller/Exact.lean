-- CamelUp.Controller.Exact
-- Exact probability computation via full die-sequence enumeration.
--
-- For a state with k dice remaining in the bag, there are k! × 3^k possible
-- die sequences (each permutation of the bag × each value assignment).
-- For k = 5: 5! × 243 = 29,160 sequences.  All are solved exactly in < 1 s.
--
-- API:
--   allDieSeqs (bag)           — enumerate every (camel, face) sequence
--   exactLegWinCounts (gs)     — (WinCounts, totalSeqs)  for the current leg
--   exactLegWinProbs  (gs)     — Float probability per camel (0..1)
import CamelUp.Model.Types
import CamelUp.Model.Step
import CamelUp.Controller.Sim

namespace CamelUp.Exact

open CamelUp CamelUp.Sim

-- ─── Sequence enumeration ────────────────────────────────────────────────────

-- All permutations of a list (no duplicates assumed).
-- Fuel-based permutation generator (fuel = list length; avoids termination proof).
private def permsAux : Nat → List CamelColor → List (List CamelColor)
  | 0,     _  => [[]]
  | _,     [] => [[]]
  | k + 1, cs =>
    cs.foldl (fun acc c =>
      let rest := cs.erase c
      acc ++ (permsAux k rest).map (fun t => c :: t)) []

private def perms (cs : List CamelColor) : List (List CamelColor) :=
  permsAux cs.length cs

-- All lists of n die values (3^n entries).
private def allVals : Nat → List (List DieValue)
  | 0     => [[]]
  | n + 1 =>
    DieValue.all.foldl (fun acc v =>
      acc ++ (allVals n).map (fun t => v :: t)) []

-- Zip a camel permutation with a value assignment into a DieOutcome sequence.
private def zipOutcomes (camels : List CamelColor) (vals : List DieValue)
    : List DieOutcome :=
  let rec go : List CamelColor → List DieValue → List DieOutcome
    | [],      _      => []
    | _ :: _,  []     => []
    | c :: cs, v :: vs => { camel := c, value := v } :: go cs vs
  go camels vals

/-- All possible die sequences from `bag` (|bag|! × 3^|bag| entries). -/
def allDieSeqs (bag : List CamelColor) : List (List DieOutcome) :=
  let bagPerms := perms bag
  bagPerms.foldl (fun acc perm =>
    let valueLists := allVals perm.length
    acc ++ valueLists.map (zipOutcomes perm)) []

-- ─── Leg-winner simulation ───────────────────────────────────────────────────

-- Apply a fixed die sequence to a game state, returning the leg-winner camel.
-- Halts early once the bag is empty (leg ends) or the race is over.
private def runLegSeq (gs : GameState) (seq : List DieOutcome) : Option CamelColor :=
  let rec go (s : GameState) (remaining : List DieOutcome) : Option CamelColor :=
    if s.gameOver then s.raceWinner
    else if s.diceBag.isEmpty then
      (legRanking s.board s.finishedCamels).head?
    else
      match remaining with
      | []          => (legRanking s.board s.finishedCamels).head?
      | o :: rest   =>
          match step s (Move.Roll o) with
          | none    => (legRanking s.board s.finishedCamels).head?
          | some s' => go s' rest
  go gs seq

-- ─── WinCounts helpers ───────────────────────────────────────────────────────

private def wcGet (wc : WinCounts) (c : CamelColor) : Nat :=
  match wc.find? (fun p => p.1 == c) with
  | none        => 0
  | some (_, n) => n

private def wcSet (wc : WinCounts) (c : CamelColor) (n : Nat) : WinCounts :=
  if wc.any (fun p => p.1 == c) then
    wc.map (fun p => if p.1 == c then (c, n) else p)
  else
    wc ++ [(c, n)]

-- ─── Main API ────────────────────────────────────────────────────────────────

/-- Enumerate every die sequence from `gs.diceBag`, simulate to leg-end,
    tally which camel leads.  Returns (WinCounts, totalSeqs). -/
def exactLegWinCounts (gs : GameState) : WinCounts × Nat :=
  let seqs  := allDieSeqs gs.diceBag
  let total := seqs.length
  let init  : WinCounts := CamelColor.all.map (fun c => (c, 0))
  let counts := seqs.foldl (fun wc seq =>
    match runLegSeq gs seq with
    | none   => wc
    | some c => wcSet wc c (wcGet wc c + 1)) init
  (counts, total)

/-- Exact leg-win probability for each camel (as Float in 0..1).
    Returns a list of (CamelColor, prob) sorted by probability descending. -/
def exactLegWinProbs (gs : GameState) : List (CamelColor × Float) :=
  let (counts, total) := exactLegWinCounts gs
  let totF := (total : Nat).toFloat
  let probs := counts.map (fun (c, n) =>
    (c, if total == 0 then 0.0 else (n : Nat).toFloat / totF))
  let rec insertDesc : List (CamelColor × Float) → (CamelColor × Float) → List (CamelColor × Float)
    | [],     x => [x]
    | h :: t, x => if x.2 >= h.2 then x :: h :: t else h :: insertDesc t x
  probs.foldl (fun acc p => insertDesc acc p) []

/-- Format exact probabilities as a multi-line string (like winCountsToString). -/
def exactProbsToString (gs : GameState) : String :=
  let (counts, total) := exactLegWinCounts gs
  let lines := counts.map (fun (c, n) =>
    let pctNum := if total = 0 then 0 else (n * 1000 + total / 2) / total
    let whole  := pctNum / 10
    let frac   := pctNum % 10
    s!"  {c}: {n}/{total}  ({whole}.{frac}%)")
  String.intercalate "\n" lines

end CamelUp.Exact
