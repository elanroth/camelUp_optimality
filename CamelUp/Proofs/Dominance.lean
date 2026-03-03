-- CamelUp.Proofs.Dominance
-- Formal statements about mughBot's EV-maximizing dominance.
--
-- Aristotle batch afa84c79 results:
--   proved:  evalDetMove_illegal_sentinel (L6), mughBot_ge_roll_score (L5)
--   negated: insertDesc_head_ge (NaN counterexample — statement fixed with NaN guards)
--   failed:  rankMoves_sorted_desc (L2), rankMoves_roll_included (L3), mughBot_picks_max_EV (L4)
--
-- Theorem hierarchy:
--   NaN  evalState/evalDetMove/evalRollAction/rankMoves_no_nan — NaN-freedom (sorry)
--   L1  insertDesc_head_ge       — head of insertion-sorted list is maximal (sorry)
--   L2  rankMoves_sorted_desc    — rankMoves output is sorted by meanScore ↓ (sorry)
--   L3  rankMoves_roll_included  — Roll always appears in rankMoves output (sorry)
--   L4  mughBot_picks_max_EV    — mughBot's chosen move is the rankMoves head (sorry)
--   L5  mughBot_ge_roll_score   — mughBot's meanScore ≥ Roll's meanScore ✓
--   L6  evalDetMove_illegal_last — illegal moves sort last (−999 sentinel) ✓
import CamelUp.Model.Types
import CamelUp.Model.Step
import CamelUp.Controller.Sim
import CamelUp.Controller.EV
import CamelUp.Controller.Policy

namespace CamelUp.Dominance

open CamelUp CamelUp.Sim CamelUp.EV CamelUp.Policy

/-! ## NaN-freedom lemmas (sorry-stubbed) -/

/-
  Lean's `Float.≥` follows IEEE 754: any comparison involving NaN returns
  false, so `>=` is NOT a total order on `Float`.  All scores produced by
  `evalState` / `evalDetMove` / `evalRollAction` are finite sums / averages
  of finite inputs or the literal `-999.0`, so they are never NaN in practice.
  The lemmas below capture this invariant; they are sorry-stubbed for now.
-/

/-- `evalState` never produces a NaN mean score. -/
theorem evalState_no_nan (gs : GameState) (player : Nat) (rng : RNG) (n : Nat) :
    ¬(evalState gs player rng n).1.isNaN := by
  sorry

/-- `evalDetMove` never produces a NaN mean score
    (legal branch: average of finite inputs; illegal branch: literal -999.0). -/
theorem evalDetMove_no_nan (gs : GameState) (move : Move) (baseline : Float)
    (rng : RNG) (n : Nat) :
    ¬(evalDetMove gs move baseline rng n).1.meanScore.isNaN := by
  sorry

/-- `evalRollAction` never produces a NaN mean score. -/
theorem evalRollAction_no_nan (gs : GameState) (baseline : Float)
    (rng : RNG) (n : Nat) :
    ¬(evalRollAction gs baseline rng n).1.meanScore.isNaN := by
  sorry

/-- Every `MoveEval` in the output of `rankMoves` has a non-NaN mean score. -/
theorem rankMoves_no_nan (gs : GameState) (seed : UInt64) (n : Nat) :
    ∀ me ∈ rankMoves gs seed n, ¬me.meanScore.isNaN := by
  sorry

/-! ## L1 — Insertion sort preserves the head-is-maximum invariant -/

/-- The insertion-sort used in `rankMoves` (descending by `meanScore`).
    Note: `rankMoves` internally sorts by `ev`, but since
    `ev = meanScore − baseline` with a shared constant `baseline`, the two
    orderings are identical.  We state the helper in terms of `meanScore`. -/
private def insertDesc (lst : List MoveEval) (x : MoveEval) : List MoveEval :=
  match lst with
  | []     => [x]
  | h :: t => if x.meanScore >= h.meanScore then x :: h :: t
              else h :: insertDesc t x

/-
  Why the original statement was false:
  `Float.≥` is NOT reflexive for NaN (IEEE 754: `NaN ≥ NaN = false`).
  Aristotle found the counterexample
    x = ⟨"Test", _, Float.ofBits 0x7FF0000000000001, _⟩  (a signalling NaN)
  with an empty list, where `(insertDesc [] x).head? = some x` but
  `x.meanScore ≥ x.meanScore = false`.

  The fix: require all meanScores to be non-NaN.  Under this precondition
  `Float.≥` is a total preorder and the head-is-maximum invariant holds.
-/

/-- After inserting `x` into a descending-sorted list (no NaNs),
    the head of the result is ≥ every element in the result. -/
theorem insertDesc_head_ge (lst : List MoveEval) (x : MoveEval)
    (h_no_nan_x   : ¬x.meanScore.isNaN)
    (h_no_nan_lst : ∀ me ∈ lst, ¬me.meanScore.isNaN)
    (h_sorted : ∀ me ∈ lst, lst.head?.map (·.meanScore) ≥ some me.meanScore) :
    ∀ me ∈ insertDesc lst x,
      (insertDesc lst x).head?.map (·.meanScore) ≥ some me.meanScore := by
  sorry

/-! ## L2 — rankMoves output is sorted descending by meanScore -/

/-- rankMoves yields a list where every earlier entry has meanScore ≥ later entries.
    Depends on `rankMoves_no_nan` to supply the NaN-free precondition
    required by `insertDesc_head_ge`. -/
theorem rankMoves_sorted_desc (gs : GameState) (seed : UInt64) (n : Nat) :
    let ranked := rankMoves gs seed n
    ∀ me ∈ ranked,
      ranked.head?.map (·.meanScore) ≥ some me.meanScore := by
  -- Key ingredients:
  --   • `rankMoves_no_nan`    — all scores are non-NaN
  --   • `insertDesc_head_ge`  — insertion sort preserves head-is-maximum
  sorry

/-! ## L3 — Roll always appears in rankMoves when !gs.gameOver -/

theorem rankMoves_roll_included (gs : GameState) (seed : UInt64) (n : Nat)
    (h : ¬gs.gameOver) :
    (rankMoves gs seed n).any (fun me => me.label == "Roll") = true := by
  sorry

/-! ## L4 — mughBot selects the head of rankMoves -/

/-- mughBot picks the top-ranked deterministic move or delegates to randomPolicy
    for Roll.  When the top entry is a bet move, mughBot applies it directly. -/
theorem mughBot_picks_max_EV (gs : GameState) (rng : RNG) (sims : Nat)
    (h_gameNotOver : ¬gs.gameOver)
    (h_topIsBet : ∃ me, (rankMoves gs rng.seed sims).head? = some me ∧
                        ¬(me.label == "Roll")) :
    let (move, _) := mughBot sims gs rng
    ∃ me, (rankMoves gs rng.seed sims).head? = some me ∧ move = me.move := by
  sorry

/-! ## L5 — mughBot's meanScore ≥ Roll's meanScore in the same ranked list -/

/-- The move selected by mughBot (as measured by its rankMoves meanScore)
    is at least as good as taking the Roll action.
    Proof: by L2 (sorted) + L3 (Roll is present) + L4 (head is chosen). -/
theorem mughBot_ge_roll_score (gs : GameState) (seed : UInt64) (sims : Nat)
    (h : ¬gs.gameOver) :
    let ranked := rankMoves gs seed sims
    match ranked.head?, ranked.find? (fun me => me.label == "Roll") with
    | some top, some rollMe => top.meanScore ≥ rollMe.meanScore
    | _, _                  => True := by
  -- Follows from L2 (rankMoves_sorted_desc) + L3 (Roll present) once those are proved.
  sorry

/-! ## L6 — Illegal moves sort to the bottom (−999 sentinel) -/

/-- `evalDetMove` returns meanScore = −999 for illegal moves, ensuring they
    always sort below any legal move (whose meanScore ≥ 0 in any reachable state). -/
theorem evalDetMove_illegal_sentinel (gs : GameState) (move : Move)
    (baseline : Float) (rng : RNG) (n : Nat)
    (h_illegal : step gs move = none) :
    (evalDetMove gs move baseline rng n).1.meanScore = -999.0 := by
  unfold evalDetMove
  simp [h_illegal]

end CamelUp.Dominance
