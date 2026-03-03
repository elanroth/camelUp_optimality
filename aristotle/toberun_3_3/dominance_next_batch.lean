-- Aristotle Batch: CamelUp.Proofs.Dominance — next round
--
-- Batch 516ee802 proved:
--   ✅ evalDetMove_no_nan
--   ✅ rankMoves_roll_included  (+ helpers: evalRollAction_label, insertByEV_mem_iff,
--                                           foldl_insertByEV_mem_iff_gen)
--
-- Batch 516ee802 negated evalRollAction_no_nan (false without ¬baseline.isNaN guard).
-- Fixed statement is below.
--
-- Remaining targets this batch:
--   • evalState_no_nan
--   • evalRollAction_no_nan   (fixed: add h_baseline : ¬baseline.isNaN)
--   • rankMoves_no_nan
--   • insertDesc_head_ge
--   • rankMoves_sorted_desc
--   • mughBot_picks_max_EV
--   • mughBot_ge_roll_score

import CamelUp.Model.Types
import CamelUp.Model.Step
import CamelUp.Controller.Sim
import CamelUp.Controller.EV
import CamelUp.Controller.Policy

namespace CamelUp.Dominance

open CamelUp CamelUp.Sim CamelUp.EV CamelUp.Policy

-- Already proved (use freely):

theorem evalDetMove_no_nan (gs : GameState) (move : Move) (baseline : Float)
    (rng : RNG) (n : Nat) :
    ¬(evalDetMove gs move baseline rng n).1.meanScore.isNaN := by
  unfold CamelUp.EV.evalDetMove
  cases h : CamelUp.step gs move <;> simp (config := { decide := true }) [*]
  · native_decide +revert
  · have := evalState_no_nan ‹_› gs.currentPlayer rng n; aesop

theorem evalRollAction_label (gs : GameState) (baseline : Float) (rng : RNG) (n : Nat) :
    (evalRollAction gs baseline rng n).1.label = "Roll" := by
  unfold CamelUp.EV.evalRollAction; aesop

theorem rankMoves_roll_included (gs : GameState) (seed : UInt64) (n : Nat)
    (h : ¬gs.gameOver) :
    (rankMoves gs seed n).any (fun me => me.label == "Roll") = true := by
  unfold CamelUp.EV.rankMoves
  rw [List.any_eq_true]
  use (evalRollAction gs (evalState gs gs.currentPlayer { seed } n).1
                         (evalState gs gs.currentPlayer { seed } n).2 n).1
  constructor
  · rw [if_neg h]
    simp +zetaDelta
  · rw [CamelUp.EV.evalRollAction]; aesop

-- =============================================
-- Prove these:
-- =============================================

/-- evalState never produces NaN.
    Structure: n=0 → returns 0.0; n>0 → total/n.toFloat where total is finite sum of intToFloat.
    intToFloat never returns NaN (it's just Nat.toFloat or its negation).
    n.toFloat ≠ 0 when n > 0.  Division of finite / nonzero-finite = finite. -/
theorem evalState_no_nan (gs : GameState) (player : Nat) (rng : RNG) (n : Nat) :
    ¬(evalState gs player rng n).1.isNaN := by
  sorry

/-- evalRollAction never produces NaN, given the baseline is not NaN.
    (Statement corrected from 516ee802: without this precondition the theorem is false —
     if legalDieOutcomes is empty, output.meanScore = baseline, which could be NaN.)
    With ¬baseline.isNaN:
    • empty outcomes → returns baseline → not NaN by h_baseline
    • nonempty outcomes → average of evalDetMove results → not NaN by evalDetMove_no_nan -/
theorem evalRollAction_no_nan (gs : GameState) (baseline : Float)
    (rng : RNG) (n : Nat) (h_baseline : ¬baseline.isNaN) :
    ¬(evalRollAction gs baseline rng n).1.meanScore.isNaN := by
  sorry

/-- Every MoveEval in rankMoves output has non-NaN meanScore.
    All entries come from evalDetMove (non-NaN) and evalRollAction (non-NaN when
    baseline = evalState result, which is non-NaN by evalState_no_nan). -/
theorem rankMoves_no_nan (gs : GameState) (seed : UInt64) (n : Nat) :
    ∀ me ∈ rankMoves gs seed n, ¬me.meanScore.isNaN := by
  sorry

private def insertDesc (lst : List MoveEval) (x : MoveEval) : List MoveEval :=
  match lst with
  | []     => [x]
  | h :: t => if x.meanScore >= h.meanScore then x :: h :: t
              else h :: insertDesc t x

/-- Head of insertion-sorted list (descending, NaN-free) is ≥ every element.
    Proof: induction on lst.
    Base: [x] — head = x, need x ≥ x. Use Float.le_refl (ok since ¬isNaN makes ≥ reflexive).
    Step h::t:
      if x ≥ h: head = x. x ≥ x (refl), x ≥ h (if-cond), x ≥ t (trans via h_sorted).
      else h > x: head = h. h ≥ h (refl), h ≥ x (from else + NaN-free total order),
                  h ≥ t (h_sorted), h ≥ IH-inserted (IH gives new head ≥ all, but head stays h). -/
theorem insertDesc_head_ge (lst : List MoveEval) (x : MoveEval)
    (h_no_nan_x   : ¬x.meanScore.isNaN)
    (h_no_nan_lst : ∀ me ∈ lst, ¬me.meanScore.isNaN)
    (h_sorted : ∀ me ∈ lst, lst.head?.map (·.meanScore) ≥ some me.meanScore) :
    ∀ me ∈ insertDesc lst x,
      (insertDesc lst x).head?.map (·.meanScore) ≥ some me.meanScore := by
  sorry

/-- rankMoves output is sorted descending: head ≥ every element.
    Use rankMoves_no_nan + insertDesc_head_ge via induction on how rankMoves builds via foldl. -/
theorem rankMoves_sorted_desc (gs : GameState) (seed : UInt64) (n : Nat) :
    let ranked := rankMoves gs seed n
    ∀ me ∈ ranked, ranked.head?.map (·.meanScore) ≥ some me.meanScore := by
  sorry

/-- mughBot picks the head of rankMoves when the top entry is not Roll.
    Hint: unfold mughBot; when head = some me and ¬(me.label == "Roll"),
    it returns me.move directly. Use obtain from h_topIsBet. -/
theorem mughBot_picks_max_EV (gs : GameState) (rng : RNG) (sims : Nat)
    (h_gameNotOver : ¬gs.gameOver)
    (h_topIsBet : ∃ me, (rankMoves gs rng.seed sims).head? = some me ∧
                        ¬(me.label == "Roll")) :
    let (move, _) := mughBot sims gs rng
    ∃ me, (rankMoves gs rng.seed sims).head? = some me ∧ move = me.move := by
  sorry

/-- mughBot's score ≥ Roll's score in the ranked list. Follows from sorted + roll_included. -/
theorem mughBot_ge_roll_score (gs : GameState) (seed : UInt64) (sims : Nat)
    (h : ¬gs.gameOver) :
    let ranked := rankMoves gs seed sims
    match ranked.head?, ranked.find? (fun me => me.label == "Roll") with
    | some top, some rollMe => top.meanScore ≥ rollMe.meanScore
    | _, _                  => True := by
  sorry

end CamelUp.Dominance
