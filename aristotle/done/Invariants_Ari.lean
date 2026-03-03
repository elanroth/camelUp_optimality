/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 51af4e3e-2178-4dc4-b395-c5eb901f048f

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem setStack_size (b : Board) (sq : Nat) (s : Stack) :
    (b.setStack sq s).size = b.size

- theorem applyDie_preserves_boardSize
    (board : Board) (mods : Array (Option ModifierTile))
    (finished : List CamelColor) (outcome : DieOutcome)
    (h : board.size = numSquares) :
    (applyDie board mods finished outcome).1.size = numSquares

- theorem resolveLegBets_scores_size
    (scores : Array Int) (ranking : List CamelColor) (bets : List LegBetEntry) :
    (resolveLegBets scores ranking bets).size = scores.size

- theorem resolveRaceWinBets_scores_size
    (scores : Array Int) (winner : CamelColor) (bets : List RaceBetEntry) :
    (resolveRaceWinBets scores winner bets).size = scores.size

The following was negated by Aristotle:

- theorem applyDie_preserves_totalCount
    (board : Board) (mods : Array (Option ModifierTile))
    (finished : List CamelColor) (outcome : DieOutcome) :
    let (board', finished', _)

- theorem applyDie_preserves_camelCount
    (board : Board) (mods : Array (Option ModifierTile))
    (finished : List CamelColor) (outcome : DieOutcome)
    (c : CamelColor) :
    let (board', finished', _)

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

-- CamelUp.Proofs.Invariants
-- Lemma statements about GameState validity.
-- All proof bodies are sorry-stubbed for Aristotle to complete.
import CamelUp.Model.Types
import CamelUp.Model.Step


namespace CamelUp

/-! ## Board.setStack preserves array size -/

theorem setStack_size (b : Board) (sq : Nat) (s : Stack) :
    (b.setStack sq s).size = b.size := by
  -- The size of the array remains the same after setting a stack at a particular square because we are only replacing elements within the array.
  have h_size : ∀ (arr : Array (List CamelColor)) (i : Nat) (v : List CamelColor), (arr.set! i v).size = arr.size := by
    aesop;
  convert h_size b sq s using 1;
  -- The `setAt` function is equivalent to `set!` because it's just a recursive version that works on the list representation of the array.
  have h_setAt_eq_set! : ∀ (arr : Array (List CamelColor)) (i : Nat) (v : List CamelColor), (arr.set! i v).toList = (CamelUp.Board.setStack.setAt v arr.toList i) := by
    intros arr i v
    simp [CamelUp.Board.setStack.setAt];
    induction arr.toList generalizing i ; aesop;
    cases i <;> aesop;
  convert congr_arg Array.size ( congr_arg Array.mk ( h_setAt_eq_set! b sq s ) ) using 1;
  · unfold CamelUp.Board.setStack; aesop;
  · rw [ ← h_setAt_eq_set! ]

/-! ## applyDie preserves invariants -/

/- Aristotle found this block to be false. Here is a proof of the negation:



/-
Conservation of camels: total count (board + finished) unchanged by a roll.
-/
theorem applyDie_preserves_totalCount
    (board : Board) (mods : Array (Option ModifierTile))
    (finished : List CamelColor) (outcome : DieOutcome) :
    let (board', finished', _) := applyDie board mods finished outcome
    (List.range numSquares).foldl (fun acc i => acc + (board'.getStack i).length) 0
      + finished'.length =
    (List.range numSquares).foldl (fun acc i => acc + (board.getStack i).length) 0
      + finished.length := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Consider a board with one camel on square 0.
  use (List.replicate 1 [CamelColor.White]).toArray;
  -- Consider a modifier tile on square 0.
  use (List.replicate 1 (some { owner := 0, effect := 1 })).toArray;
  -- Consider a finished list with one camel.
  use [CamelColor.White];
  -- Consider a die outcome with a value of 1.
  use ⟨CamelColor.White, 1⟩;
  -- Let's simplify the goal.
  simp (config := { decide := true }) only [List.foldl]

-/
/-- Conservation of camels: total count (board + finished) unchanged by a roll. -/
theorem applyDie_preserves_totalCount
    (board : Board) (mods : Array (Option ModifierTile))
    (finished : List CamelColor) (outcome : DieOutcome) :
    let (board', finished', _) := applyDie board mods finished outcome
    (List.range numSquares).foldl (fun acc i => acc + (board'.getStack i).length) 0
      + finished'.length =
    (List.range numSquares).foldl (fun acc i => acc + (board.getStack i).length) 0
      + finished.length := by
  sorry

theorem applyDie_preserves_boardSize
    (board : Board) (mods : Array (Option ModifierTile))
    (finished : List CamelColor) (outcome : DieOutcome)
    (h : board.size = numSquares) :
    (applyDie board mods finished outcome).1.size = numSquares := by
  -- The setStack function does not change the size of the array, so the length of the modified board is equal to the original board's length.
  have h_setStack_size : ∀ (b : Board) (sq : Nat) (s : Stack), (b.setStack sq s).size = b.size := by
    exact?;
  unfold CamelUp.applyDie; aesop;

/- Aristotle found this block to be false. Here is a proof of the negation:



theorem applyDie_preserves_camelCount
    (board : Board) (mods : Array (Option ModifierTile))
    (finished : List CamelColor) (outcome : DieOutcome)
    (c : CamelColor) :
    let (board', finished', _) := applyDie board mods finished outcome
    finished'.count c +
    (List.range numSquares).foldl (fun acc i => acc + (board'.getStack i).count c) 0 =
    finished.count c +
    (List.range numSquares).foldl (fun acc i => acc + (board.getStack i).count c) 0 := by
  -- Apply the `setStack_size` theorem to show that the size of the board remains the same.
  have h_size : (applyDie board mods finished outcome).1.size = board.size := by sorry;
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Set up the initial board with one white camel at position 0.
  use #[[CamelColor.White]], Array.replicate (numSquares) none, [], ⟨CamelColor.White, ⟨0, by decide⟩⟩, CamelColor.White;
  -- Let's simplify the goal.
  simp +decide [CamelUp.applyDie]

-/
theorem applyDie_preserves_camelCount
    (board : Board) (mods : Array (Option ModifierTile))
    (finished : List CamelColor) (outcome : DieOutcome)
    (c : CamelColor) :
    let (board', finished', _) := applyDie board mods finished outcome
    finished'.count c +
    (List.range numSquares).foldl (fun acc i => acc + (board'.getStack i).count c) 0 =
    finished.count c +
    (List.range numSquares).foldl (fun acc i => acc + (board.getStack i).count c) 0 := by
  sorry

/-! ## step preserves ValidState (all move types) -/

/- Aristotle failed to find a proof. -/
/-- The central safety property: every legal step preserves all ValidState invariants.

    This covers all four move types: Roll, BetLeg, BetRaceWin, BetRaceLose.
    The Roll case is the hard one (requires applyDie_preserves_camelCount et al.).
    The bet cases are straightforward since they don't touch the board. -/
theorem step_preserves_valid
    (gs : GameState) (move : Move) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs move = some gs') :
    ValidState gs' := by
  sorry

/-! ## Bet resolution corollaries -/

/-- resolveLegBets does not change array length. -/
theorem resolveLegBets_scores_size
    (scores : Array Int) (ranking : List CamelColor) (bets : List LegBetEntry) :
    (resolveLegBets scores ranking bets).size = scores.size := by
  unfold CamelUp.resolveLegBets;
  induction bets using List.reverseRecOn <;> simp +decide [ * ];
  -- By definition of `awardPlayer`, the size of the array remains the same after awarding coins.
  have h_awardPlayer_size : ∀ (scores : Array ℤ) (p : ℕ) (delta : ℤ), (CamelUp.awardPlayer scores p delta).size = scores.size := by
    intros scores p delta
    simp [CamelUp.awardPlayer];
    rename_i k; induction scores using Array.recOn ; simp +decide [ * ] ;
    rename_i l; induction l generalizing p <;> simp +decide [ * ] ;
    · cases p <;> trivial;
    · cases p <;> simp +decide [ * ];
      · exact?;
      · exact?;
  rw [ h_awardPlayer_size, ‹ ( List.foldl _ scores _ ).size = scores.size › ]

/- resolveRaceWinBets does not change array length. -/
noncomputable section AristotleLemmas

/-
awardPlayer preserves size for non-negative deltas (derived from resolveLegBets).
-/
theorem CamelUp.awardPlayer_size_nat (scores : Array Int) (p : Nat) (v : Nat) :
    (CamelUp.awardPlayer scores p v).size = scores.size := by
      convert resolveLegBets_scores_size scores [ .White ] [ ⟨ .White, v, p ⟩ ]

/-
awardPlayer preserves size for delta = -1.
-/
theorem CamelUp.awardPlayer_size_neg1 (scores : Array Int) (p : Nat) :
    (CamelUp.awardPlayer scores p (-1)).size = scores.size := by
      convert CamelUp.resolveLegBets_scores_size _ _ _;
      rotate_left;
      exact [ ];
      exact [ ⟨ .White, 5, p ⟩ ];
      unfold CamelUp.resolveLegBets; aesop;

/-
awardPlayer preserves size when the delta is a race payout.
-/
theorem CamelUp.awardPlayer_size_racePayout (scores : Array Int) (p : Nat) (i : Nat) :
    (CamelUp.awardPlayer scores p (CamelUp.racePayoutAt i)).size = scores.size := by
      convert CamelUp.awardPlayer_size_nat scores p ( List.recOn ( List.drop i [ 8, 5, 3, 2, 1 ] ) 1 fun head tail => head ) using 1;
      rcases i with ( _ | _ | _ | _ | _ | i ) <;> simp +decide [ CamelUp.racePayoutAt ] at *;
      all_goals rfl;

end AristotleLemmas

theorem resolveRaceWinBets_scores_size
    (scores : Array Int) (winner : CamelColor) (bets : List RaceBetEntry) :
    (resolveRaceWinBets scores winner bets).size = scores.size := by
  -- The foldl operation preserves the size of the scores array because each step in the fold is just modifying the array in place.
  have h_foldl_size : ∀ (bets : List CamelUp.RaceBetEntry) (scores : Array ℤ) (idx : Nat), (List.foldl (fun (pair : Array ℤ × Nat) (bet : CamelUp.RaceBetEntry) =>
    match pair with
    | (sc, idx) =>
      if bet.camel == winner then (CamelUp.awardPlayer sc bet.player (CamelUp.racePayoutAt idx), idx + 1)
      else (CamelUp.awardPlayer sc bet.player (-1), idx)) (scores, idx) bets).1.size = scores.size := by
        intro bets scores idx; induction bets using List.reverseRecOn; aesop;
        simp +zetaDelta at *;
        split_ifs <;> simp_all +decide [ CamelUp.awardPlayer_size_neg1, CamelUp.awardPlayer_size_racePayout ];
  exact h_foldl_size _ _ _

/-! ## Useful corollaries -/

theorem valid_bag_sub (gs : GameState) (h : ValidState gs) :
    ∀ c ∈ gs.diceBag, c ∈ CamelColor.all :=
  h.bag_sub

theorem valid_board_size (gs : GameState) (h : ValidState gs) :
    gs.board.size = numSquares :=
  h.board_size

theorem valid_scores_size (gs : GameState) (h : ValidState gs) :
    gs.scores.size = gs.numPlayers :=
  h.scores_size

end CamelUp