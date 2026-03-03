-- Aristotle Batch: CamelUp.Proofs.Dominance remaining sorries
--
-- All 9 theorems below are sorry-stubbed.  Prove as many as possible.
--
-- Dependency order:
--   NaN-freedom (evalState_no_nan / evalDetMove_no_nan /
--                evalRollAction_no_nan / rankMoves_no_nan)
--     ↓
--   L1: insertDesc_head_ge
--     ↓
--   L2: rankMoves_sorted_desc    (needs NaN + L1)
--   L3: rankMoves_roll_included  (needs NaN; structural)
--     ↓
--   L4: mughBot_picks_max_EV     (needs L2 + L3; structural)
--   L5: mughBot_ge_roll_score    (needs L2 + L3; corollary)
--
-- Key definitions (from CamelUp.Controller.EV):
--
--   def evalState (gs : GameState) (player : Nat) (rng : RNG) (n : Nat) : Float × RNG
--     -- n Monte-Carlo roll-outs; mean final score for `player`
--     -- body: foldl over List.range n, accumulates (sum, rng), divides by n
--     -- all individual scores come from gs'.scores.getD, shifted via intToFloat
--
--   def evalDetMove (gs : GameState) (move : Move) (baseline : Float)
--                   (rng : RNG) (n : Nat) : MoveEval × RNG
--     -- if step gs move = none → MoveEval with meanScore = -999.0 (proved: evalDetMove_illegal_sentinel)
--     -- otherwise → applies move, calls evalState on resulting state, returns MoveEval
--
--   def evalRollAction (gs : GameState) (baseline : Float)
--                      (rng : RNG) (n : Nat) : MoveEval × RNG
--     -- average over legalDieOutcomes of evalDetMove results
--
--   def rankMoves (gs : GameState) (seed : UInt64) (simsPerMove : Nat) : List MoveEval
--     -- builds list of MoveEval by calling evalDetMove / evalRollAction
--     -- inserts into descending-sorted list via insertDesc
--
--   private def insertDesc (lst : List MoveEval) (x : MoveEval) : List MoveEval
--     -- defined locally in Dominance.lean (re-stated below for Aristotle):
--     -- | []     => [x]
--     -- | h :: t => if x.meanScore >= h.meanScore then x :: h :: t
--     --             else h :: insertDesc t x
--
-- Float / NaN notes:
--   • Float in Lean follows IEEE 754:  NaN.isNaN = true, and for all finite f,
--     f.isNaN = false.
--   • Int.toNat.toFloat and intToFloat (defined in EV.lean) never produce NaN.
--   • Arithmetic on non-NaN values may produce NaN only via 0/0 or ∞−∞;
--     since all inputs are bounded, all results are finite.
--   • The guard `if n = 0 then 0.0 else total / n.toFloat` avoids 0/0.

import CamelUp.Model.Types
import CamelUp.Model.Step
import CamelUp.Controller.Sim
import CamelUp.Controller.EV
import CamelUp.Controller.Policy

namespace CamelUp.Dominance

open CamelUp CamelUp.Sim CamelUp.EV CamelUp.Policy

/-! ## NaN-freedom lemmas -/

/-- `evalState` never produces a NaN mean score.
    Hint: unfold evalState; the result is `0.0` when n=0 (literal, not NaN),
    or `total / n.toFloat` where `total` is a finite sum of `intToFloat` values.
    Try: `unfold evalState; split_ifs; simp [Float.isNaN]` -/
theorem evalState_no_nan (gs : GameState) (player : Nat) (rng : RNG) (n : Nat) :
    ¬(evalState gs player rng n).1.isNaN := by
  sorry

/-- `evalDetMove` never produces a NaN mean score.
    Hint: unfold evalDetMove; case split on `step gs move`.
    • none branch  → meanScore = -999.0, not NaN. `simp [Float.isNaN]`
    • some branch  → meanScore comes from evalState; use evalState_no_nan.
    Try: `unfold evalDetMove; split_ifs; simp [Float.isNaN]` and
         `exact evalState_no_nan ...` -/
theorem evalDetMove_no_nan (gs : GameState) (move : Move) (baseline : Float)
    (rng : RNG) (n : Nat) :
    ¬(evalDetMove gs move baseline rng n).1.meanScore.isNaN := by
  sorry

/-- `evalRollAction` never produces a NaN mean score.
    Hint: similar to evalDetMove_no_nan; unfold evalRollAction,
    the result is an average of evalDetMove meanScores (all non-NaN by
    evalDetMove_no_nan). -/
theorem evalRollAction_no_nan (gs : GameState) (baseline : Float)
    (rng : RNG) (n : Nat) :
    ¬(evalRollAction gs baseline rng n).1.meanScore.isNaN := by
  sorry

/-- Every `MoveEval` in the output of `rankMoves` has a non-NaN mean score.
    Hint: unfold rankMoves; all entries come from evalDetMove or evalRollAction,
    both proved non-NaN above.  Use `List.mem_*` lemmas + the above. -/
theorem rankMoves_no_nan (gs : GameState) (seed : UInt64) (n : Nat) :
    ∀ me ∈ rankMoves gs seed n, ¬me.meanScore.isNaN := by
  sorry

/-! ## L1 — Insertion sort preserves the head-is-maximum invariant -/

-- (Same local definition as in Dominance.lean; stated here so Aristotle can
-- reason about it without unfolding the actual rankMoves internals.)
private def insertDesc' (lst : List MoveEval) (x : MoveEval) : List MoveEval :=
  match lst with
  | []     => [x]
  | h :: t => if x.meanScore >= h.meanScore then x :: h :: t
              else h :: insertDesc' t x

/-- After inserting `x` into a descending-sorted list (all non-NaN),
    the head of the result is ≥ every element in the result.
    Hint: induction on `lst`.
    • Base (lst = []): result = [x]; head = x; x.meanScore >= x.meanScore
      follows from Float.ge_iff_le + le_refl (valid because ¬x.meanScore.isNaN).
    • Step (lst = h::t):
      – if x.meanScore >= h.meanScore: result = x::h::t; head = x.
        Need x >= x (by NaN freedom), x >= h (hypothesis), x >= everything in t
        (by h_sorted transitivity: x >= h >= t).
      – else (h.meanScore > x.meanScore, since both non-NaN):
        result = h :: insertDesc' t x; head = h.
        Need h >= x (from the else branch + NaN-total-order),
        h >= everything in t (h_sorted on t), and h >= inserted position
        (inductive hypothesis gives insertDesc' head >= new head, but head doesn't
        change here since h stays at front). -/
theorem insertDesc_head_ge (lst : List MoveEval) (x : MoveEval)
    (h_no_nan_x   : ¬x.meanScore.isNaN)
    (h_no_nan_lst : ∀ me ∈ lst, ¬me.meanScore.isNaN)
    (h_sorted : ∀ me ∈ lst, lst.head?.map (·.meanScore) ≥ some me.meanScore) :
    ∀ me ∈ insertDesc' lst x,
      (insertDesc' lst x).head?.map (·.meanScore) ≥ some me.meanScore := by
  sorry

/-! ## L2 — rankMoves output is sorted descending by meanScore -/

theorem rankMoves_sorted_desc (gs : GameState) (seed : UInt64) (n : Nat) :
    let ranked := rankMoves gs seed n
    ∀ me ∈ ranked,
      ranked.head?.map (·.meanScore) ≥ some me.meanScore := by
  -- Ingredients: rankMoves_no_nan + insertDesc_head_ge
  sorry

/-! ## L3 — Roll always appears in rankMoves when game not over -/

/-- When the game is not over there is at least one legal die outcome,
    so `evalRollAction` is called and its result is inserted into the ranked list.
    Hint: unfold rankMoves; `h : ¬gs.gameOver` means `gs.diceBag` is nonempty
    (or legalDieOutcomes is nonempty).  The Roll entry always gets a label "Roll"
    from evalRollAction.  Use List.any_iff_exists + List.mem_*. -/
theorem rankMoves_roll_included (gs : GameState) (seed : UInt64) (n : Nat)
    (h : ¬gs.gameOver) :
    (rankMoves gs seed n).any (fun me => me.label == "Roll") = true := by
  sorry

/-! ## L4 — mughBot selects the head of rankMoves -/

theorem mughBot_picks_max_EV (gs : GameState) (rng : RNG) (sims : Nat)
    (h_gameNotOver : ¬gs.gameOver)
    (h_topIsBet : ∃ me, (rankMoves gs rng.seed sims).head? = some me ∧
                        ¬(me.label == "Roll")) :
    let (move, _) := mughBot sims gs rng
    ∃ me, (rankMoves gs rng.seed sims).head? = some me ∧ move = me.move := by
  -- Hint: unfold mughBot; the implementation takes head of rankMoves and
  -- checks if label == "Roll". When head is a bet (h_topIsBet), it returns
  -- head.move directly. Use obtain from h_topIsBet to name the head me,
  -- then unfold mughBot and simp with me's properties.
  sorry

/-! ## L5 — mughBot's meanScore ≥ Roll's meanScore -/

theorem mughBot_ge_roll_score (gs : GameState) (seed : UInt64) (sims : Nat)
    (h : ¬gs.gameOver) :
    let ranked := rankMoves gs seed sims
    match ranked.head?, ranked.find? (fun me => me.label == "Roll") with
    | some top, some rollMe => top.meanScore ≥ rollMe.meanScore
    | _, _                  => True := by
  -- Hint: by rankMoves_sorted_desc, head >= every element.
  -- By rankMoves_roll_included, Roll is in the list.
  -- List.find? returns some iff List.any = true; then head >= that element.
  -- Use: rankMoves_sorted_desc, rankMoves_roll_included,
  --      List.find?_some (or List.mem_of_find?_eq_some),
  --      to get rollMe ∈ ranked, then apply sorted_desc to rollMe.
  simp only []
  have hsorted := rankMoves_sorted_desc gs seed sims
  have hroll   := rankMoves_roll_included gs seed sims h
  -- rankMoves_roll_included gives List.any = true, which means
  -- ∃ me ∈ ranked, me.label == "Roll"
  rw [List.any_eq_true] at hroll
  obtain ⟨rollMe, hmem, hlabel⟩ := hroll
  have hge := hsorted rollMe hmem
  -- Now: (rankMoves gs seed sims).head?.map ... ≥ some rollMe.meanScore
  -- and find? (fun me => me.label == "Roll") finds at least rollMe
  cases h1 : (rankMoves gs seed sims).head? with
  | none => trivial
  | some top =>
    cases h2 : (rankMoves gs seed sims).find? (fun me => me.label == "Roll") with
    | none =>
      exfalso
      rw [List.find?_eq_none] at h2
      exact h2 rollMe hmem hlabel
    | some foundMe =>
      -- hge: some top.meanScore ≥ some rollMe.meanScore
      simp [h1] at hge
      -- foundMe might differ from rollMe but both satisfy ¬isNaN and have the same bound
      have hfoundMem := List.mem_of_find?_eq_some h2
      have hge2 := hsorted foundMe hfoundMem
      simp [h1] at hge2
      -- We want top.meanScore ≥ foundMe.meanScore; hge2 gives exactly that
      exact hge2

end CamelUp.Dominance
