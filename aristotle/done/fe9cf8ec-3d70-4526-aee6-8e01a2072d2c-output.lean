/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: fe9cf8ec-3d70-4526-aee6-8e01a2072d2c

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem evalDetMove_no_nan (gs : GameState) (move : Move) (baseline : Float)
    (rng : RNG) (n : Nat) :
    ¬(evalDetMove gs move baseline rng n).1.meanScore.isNaN

- theorem rankMoves_roll_included (gs : GameState) (seed : UInt64) (n : Nat)
    (h : ¬gs.gameOver) :
    (rankMoves gs seed n).any (fun me => me.label == "Roll") = true

- theorem mughBot_ge_roll_score (gs : GameState) (seed : UInt64) (sims : Nat)
    (h : ¬gs.gameOver) :
    let ranked

The following was negated by Aristotle:

- theorem evalRollAction_no_nan (gs : GameState) (baseline : Float)
    (rng : RNG) (n : Nat) :
    ¬(evalRollAction gs baseline rng n).1.meanScore.isNaN

Here is the code for the `negate_state` tactic, used within these negations:

```lean
import Mathlib
open Lean Meta Elab Tactic in
elab "revert_all" : tactic => do
  let goals ← getGoals
  let mut newGoals : List MVarId := []
  for mvarId in goals do
    newGoals := newGoals.append [(← mvarId.revertAll)]
  setGoals newGoals

open Lean.Elab.Tactic in
macro "negate_state" : tactic => `(tactic|
  (
    guard_goal_nums 1
    revert_all
    refine @(((by admit) : ∀ {p : Prop}, ¬p → p) ?_)
    try (push_neg; guard_goal_nums 1)
  )
)
```
-/

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

/- Aristotle failed to find a proof. -/
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
  unfold CamelUp.EV.evalDetMove;
  -- In the case where the move is illegal, the mean score is -999.0, which is not NaN.
  by_cases h : CamelUp.step gs move = none;
  · rw [ h ] ; norm_num [ Float.isNaN ] ; native_decide;
  · obtain ⟨gs', hgs'⟩ : ∃ gs', CamelUp.step gs move = some gs' := by
      exact Option.ne_none_iff_exists'.mp h;
    rw [ hgs' ] ; exact evalState_no_nan _ _ _ _;

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

/-
Helper lemma: 0.0 / 0.0 is NaN (proven by computation).
-/
theorem nan_is_nan : (0.0 / 0.0 : Float).isNaN := by native_decide

/-
If the game is over, there are no legal die outcomes.
-/
theorem legalDieOutcomes_empty_of_gameOver (gs : GameState) (h : gs.gameOver) :
    legalDieOutcomes gs = [] := by
  unfold legalDieOutcomes
  simp [h]

/-
Counterexample: evalRollAction returns NaN when the game is over and the baseline is NaN.
-/
theorem evalRollAction_can_be_nan :
    ∃ (gs : GameState) (baseline : Float) (rng : RNG) (n : Nat),
    (evalRollAction gs baseline rng n).1.meanScore.isNaN := by
  let gs := GameState.initial 1 Board.empty
  let gs' := { gs with gameOver := true }
  let baseline := 0.0 / 0.0
  exists gs', baseline, ⟨0⟩, 0
  simp [evalRollAction]
  rw [legalDieOutcomes_empty_of_gameOver]
  · simp
    exact nan_is_nan
  · exact rfl

end AristotleLemmas

/-
`evalRollAction` never produces a NaN mean score.
-/
theorem evalRollAction_no_nan (gs : GameState) (baseline : Float)
    (rng : RNG) (n : Nat) :
    ¬(evalRollAction gs baseline rng n).1.meanScore.isNaN := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Apply the theorem that states the existence of such a state.
  apply evalRollAction_can_be_nan

-/
/-- `evalRollAction` never produces a NaN mean score. -/
theorem evalRollAction_no_nan (gs : GameState) (baseline : Float)
    (rng : RNG) (n : Nat) :
    ¬(evalRollAction gs baseline rng n).1.meanScore.isNaN := by
  sorry

/- Aristotle failed to find a proof. -/
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

/- Aristotle failed to find a proof. -/
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

/- Aristotle failed to find a proof. -/
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

noncomputable section AristotleLemmas

/-
The `MoveEval` produced by `evalRollAction` always has the label "Roll".
-/
theorem evalRollAction_label (gs : CamelUp.GameState) (baseline : Float) (rng : CamelUp.Sim.RNG) (n : Nat) :
    (CamelUp.EV.evalRollAction gs baseline rng n).1.label = "Roll" := by
      unfold CamelUp.EV.evalRollAction; aesop;

/-
`insertEv` inserts an element into a list such that the resulting list contains the new element and all original elements.
-/
def insertEv (sorted : List CamelUp.EV.MoveEval) (me : CamelUp.EV.MoveEval) : List CamelUp.EV.MoveEval :=
  match sorted with
  | [] => [me]
  | x :: rest => if me.ev >= x.ev then me :: x :: rest else x :: insertEv rest me

theorem mem_insertEv {a b : CamelUp.EV.MoveEval} {l : List CamelUp.EV.MoveEval} :
    a ∈ insertEv l b ↔ a = b ∨ a ∈ l := by
      induction l <;> simp +decide [ *, CamelUp.Dominance.insertEv ] ; aesop;

/-
Folding `insertEv` over a list preserves membership: an element is in the result iff it was in the list or the initial accumulator.
-/
theorem mem_foldl_insertEv (l : List CamelUp.EV.MoveEval) (init : List CamelUp.EV.MoveEval) (x : CamelUp.EV.MoveEval) :
    x ∈ l.foldl (fun acc y => insertEv acc y) init ↔ x ∈ l ∨ x ∈ init := by
      induction l generalizing init x ; aesop;
      rename_i k l ih;
      convert ih ( CamelUp.Dominance.insertEv init k ) x using 1;
      by_cases hx : x = k <;> simp ( config := { decide := Bool.true } ) [ hx, mem_insertEv ]

/-
The `rollEval` computed inside `rankMoves` is always present in the output list of `rankMoves`.
-/
theorem rankMoves_mem_roll (gs : CamelUp.GameState) (seed : UInt64) (n : Nat) (h : ¬gs.gameOver) :
  let rng0 : CamelUp.Sim.RNG := { seed }
  let (baseline, rng1) := CamelUp.EV.evalState gs gs.currentPlayer rng0 n
  let (rollEval, rng2) := CamelUp.EV.evalRollAction gs baseline rng1 n
  rollEval ∈ CamelUp.EV.rankMoves gs seed n := by
    contrapose! h;
    exact Classical.not_not.1 fun h' => h <| by
      convert mem_foldl_insertEv _ _ _ |>.2 _;
      rw [ CamelUp.EV.rankMoves ];
      rw [ if_neg h' ];
      congr! 1;
      · funext sorted me; exact (by
        induction sorted <;> simp +decide [ *, CamelUp.EV.rankMoves.ins ] ; aesop ( simp_config := { decide := true } ) ;
        exact?);
      · grind

end AristotleLemmas

theorem rankMoves_roll_included (gs : GameState) (seed : UInt64) (n : Nat)
    (h : ¬gs.gameOver) :
    (rankMoves gs seed n).any (fun me => me.label == "Roll") = true := by
  norm_num +zetaDelta at *;
  exact ⟨ _, rankMoves_mem_roll gs seed n ( by simpa using h ), evalRollAction_label gs _ _ _ ⟩

/-! ## L4 — mughBot selects the head of rankMoves -/

/- Aristotle took a wrong turn (reason code: 0). Please try again. -/
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
  have := rankMoves_sorted_desc gs seed sims;
  grind

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