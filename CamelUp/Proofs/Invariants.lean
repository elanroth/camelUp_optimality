-- CamelUp.Proofs.Invariants
-- Lemma statements about GameState validity.
-- Aristotle batch dd3275b3 proved applyDie_preserves_totalCount and
-- applyDie_preserves_camelCount (plus all helper lemmas).
-- Remaining sorry: step_preserves_valid.
import Mathlib
import CamelUp.Model.Types
import CamelUp.Model.Step

namespace CamelUp

/-! ## Board.setStack preserves array size -/

theorem setStack_size (b : Board) (sq : Nat) (s : Stack) :
    (b.setStack sq s).size = b.size := by
  have h_size : ∀ (arr : Array (List CamelColor)) (i : Nat) (v : List CamelColor),
      (arr.set! i v).size = arr.size := by aesop
  convert h_size b sq s using 1
  have h_setAt_eq : ∀ (arr : Array (List CamelColor)) (i : Nat) (v : List CamelColor),
      (arr.set! i v).toList = (CamelUp.Board.setStack.setAt v arr.toList i) := by
    intros arr i v
    simp
    induction arr.toList generalizing i; aesop
    cases i <;> aesop
  convert congr_arg Array.size (congr_arg Array.mk (h_setAt_eq b sq s)) using 1
  · unfold CamelUp.Board.setStack; aesop
  · rw [← h_setAt_eq]

/-! ## applyDie preserves invariants -/

/- Conservation of camels: total count (board + finished) unchanged by a roll. -/
noncomputable section AristotleLemmas

/-
Updating a list of lists at index `i` changes the sum of lengths. Specifically,
the new sum plus the old length at `i` equals the old sum plus the new length.
This formulation avoids natural number subtraction issues.
-/
theorem List.sum_map_length_set_add {α} (L : List (List α)) (i : Nat) (s : List α) (h : i < L.length) :
    ((L.set i s).map List.length).sum + (L.get ⟨i, h⟩).length = (L.map List.length).sum + s.length := by
  induction' L with hd tl ih generalizing i s <;> simp_all ( config := { decide := Bool.true } );
  · contradiction;
  · rcases i with ( _ | i ) <;> simp_all ( config := { decide := Bool.true } ) [ List.set ];
    · ring;
    · linarith [ ih i s ( by simpa using h ) ]

/-- `Board.setStack` is equivalent to `List.set` on the underlying list. -/
theorem setStack_eq_set (b : Board) (sq : Nat) (s : Stack) :
    (b.setStack sq s).toList = b.toList.set sq s := by
  unfold CamelUp.Board.setStack;
  induction' b.toList with l ih generalizing sq;
  · cases sq <;> aesop;
  · cases sq <;> simp_all +decide [ CamelUp.Board.setStack.setAt ]

/--
The sum of stack lengths on the board computed via `foldl` over indices is equal
to the sum of lengths of the list of stacks.
-/
theorem board_sum_eq_foldl (b : Board) :
    (List.range b.size).foldl (fun acc i => acc + (b.getStack i).length) 0 = (b.toList.map List.length).sum := by
  have h_eq : List.foldl (fun acc i => acc + List.length (b.getStack i)) 0 (List.range (Array.size b)) = List.sum (List.map (fun i => List.length (b.getStack i)) (List.range (Array.size b))) := by
    induction' ( List.range b.size ) using List.reverseRecOn with l ih <;> simp +decide [ * ];
  rw [ h_eq ];
  have h_sum_eq : List.map (fun i => List.length (b.getStack i)) (List.range (Array.size b)) = List.map (fun s => List.length s) b.toList := by
    refine' List.ext_get _ _ <;> simp +decide [ CamelUp.Board.getStack ];
    aesop;
  rw [h_sum_eq]

/-- Updating a stack on the board changes the total camel count by the difference in stack lengths. -/
theorem sum_setStack_helper (b : Board) (sq : Nat) (s : Stack) (h : sq < numSquares) (hb : b.size = numSquares) :
    ((b.setStack sq s).toList.map List.length).sum + (b.getStack sq).length = (b.toList.map List.length).sum + s.length := by
  rw [ CamelUp.setStack_eq_set ];
  convert List.sum_map_length_set_add b.toList sq s _ using 1;
  all_goals norm_num [ hb, h ];
  unfold CamelUp.Board.getStack; aesop;

end AristotleLemmas

theorem applyDie_preserves_totalCount
    (board : Board) (mods : Array (Option ModifierTile))
    (finished : List CamelColor) (outcome : DieOutcome)
    (h : board.size = numSquares) :
    let (board', finished', _) := applyDie board mods finished outcome
    (List.range numSquares).foldl (fun acc i => acc + (board'.getStack i).length) 0
      + finished'.length =
    (List.range numSquares).foldl (fun acc i => acc + (board.getStack i).length) 0
      + finished.length := by
  unfold CamelUp.applyDie;
  rcases h : CamelUp.findCamelOnBoard board outcome.camel with ( _ | ⟨ sq, idx ⟩ ) <;> simp +decide;
  split_ifs <;> simp +decide;
  · have h_sum_setStack : ((board.setStack sq (List.take idx (board.getStack sq))).toList.map List.length).sum + (board.getStack sq).length = (board.toList.map List.length).sum + (List.take idx (board.getStack sq)).length := by
      apply_rules [ CamelUp.sum_setStack_helper ];
      contrapose! h; simp_all +decide [ CamelUp.findCamelOnBoard ] ;
      have h_contra : ∀ {l : List ℕ}, (∀ sq ∈ l, sq < CamelUp.numSquares) → ∀ {c : CamelUp.CamelColor}, ∀ {acc : Option (ℕ × ℕ)}, CamelUp.findCamelOnBoard.searchSquares board c l = acc → acc = none ∨ ∃ sq' idx', acc = some (sq', idx') ∧ sq' < CamelUp.numSquares := by
        intros l hl c acc hacc; induction' l with sq l ih generalizing acc <;> simp_all +decide [ CamelUp.findCamelOnBoard.searchSquares ] ;
        cases h : CamelUp.findCamelOnBoard.searchSquares.searchStack c ( board.getStack sq ) 0 <;> aesop;
      grind;
    have h_sum_setStack : (List.foldl (fun acc i => acc + List.length ((board.setStack sq (List.take idx (board.getStack sq))).getStack i)) 0 (List.range CamelUp.numSquares)) = (List.map List.length (board.setStack sq (List.take idx (board.getStack sq))).toList).sum := by
      convert CamelUp.board_sum_eq_foldl _ using 1;
      rw [ ← ‹Array.size board = CamelUp.numSquares›, CamelUp.setStack_size ]
    have h_sum_setStack' : (List.foldl (fun acc i => acc + List.length (board.getStack i)) 0 (List.range CamelUp.numSquares)) = (List.map List.length board.toList).sum := by
      convert CamelUp.board_sum_eq_foldl board using 1 ; aesop;
    simp_all +decide ;
    cases min_cases idx ( List.length ( board.getStack sq ) ) <;> simp_all +decide ; linarith [ Nat.sub_add_cancel ( show idx ≤ List.length ( board.getStack sq ) from by
                                                                                                                                                          assumption ) ] ;
  · rcases outcome with ⟨ _ | _, _ | _ ⟩ <;> simp_all +decide [ CamelUp.DieValue.toNat ];
  · cases outcome.value ; simp_all +decide [ CamelUp.DieValue.toNat ];
  · have h_sum_setStack : ((board.setStack sq (List.take idx (board.getStack sq))).toList.map List.length).sum + (board.getStack sq).length = (board.toList.map List.length).sum + (List.take idx (board.getStack sq)).length := by
      apply CamelUp.sum_setStack_helper;
      · linarith [ outcome.value.toNat ];
      · assumption;
    have h_sum_setStack : ((board.setStack sq (List.take idx (board.getStack sq))).toList.map List.length).sum + List.length (List.drop idx (board.getStack sq)) = (board.toList.map List.length).sum := by
      linarith [ show List.length ( List.take idx ( board.getStack sq ) ) + List.length ( List.drop idx ( board.getStack sq ) ) = List.length ( board.getStack sq ) from by rw [ List.length_take, List.length_drop ] ; omega ];
    convert congr_arg ( · + finished.length ) h_sum_setStack using 1 <;> ring!;
    · rw [ show List.foldl ( fun acc i => acc + List.length ( ( board.setStack sq ( List.take idx ( board.getStack sq ) ) ).getStack i ) ) 0 ( List.range CamelUp.numSquares ) = List.sum ( List.map List.length ( board.setStack sq ( List.take idx ( board.getStack sq ) ) ).toList ) from ?_ ] ; ring!;
      · rw [ List.length_drop ];
      · convert CamelUp.board_sum_eq_foldl _ using 1;
        rw [ setStack_size ] ; aesop;
    · rw [ add_comm, ← CamelUp.board_sum_eq_foldl ];
      rw [ ‹Array.size board = CamelUp.numSquares› ];
  · have h_sum_setStack : ∀ (b : CamelUp.Board) (sq : Nat) (s : CamelUp.Stack),
        sq < CamelUp.numSquares → b.size = CamelUp.numSquares →
        (List.foldl (fun acc i => acc + (CamelUp.Board.getStack (CamelUp.Board.setStack b sq s) i).length) 0 (List.range CamelUp.numSquares)) +
        (CamelUp.Board.getStack b sq).length =
        (List.foldl (fun acc i => acc + (CamelUp.Board.getStack b i).length) 0 (List.range CamelUp.numSquares)) +
        s.length := by
          intros b sq s hsq hb; exact (by
          convert CamelUp.sum_setStack_helper b sq s hsq hb using 1;
          · rw [ ← CamelUp.board_sum_eq_foldl ];
            rw [ setStack_size, hb ];
          · rw [ ← CamelUp.board_sum_eq_foldl ];
            rw [ hb ]);
    have := h_sum_setStack board sq ( List.take idx ( board.getStack sq ) ) ( by linarith ) ‹_›; have := h_sum_setStack ( board.setStack sq ( List.take idx ( board.getStack sq ) ) ) ( match mods[sq + outcome.value.toNat]?.getD Option.none with | Option.none => sq + outcome.value.toNat | Option.some tile => if 0 < tile.effect then sq + outcome.value.toNat + 1 else sq + outcome.value.toNat - 1 ) ( ( board.setStack sq ( List.take idx ( board.getStack sq ) ) ).getStack ( match mods[sq + outcome.value.toNat]?.getD Option.none with | Option.none => sq + outcome.value.toNat | Option.some tile => if 0 < tile.effect then sq + outcome.value.toNat + 1 else sq + outcome.value.toNat - 1 ) ++ List.drop idx ( board.getStack sq ) ) ( by
      grind +ring ) ( by
      rw [ setStack_size ] ; aesop ) ; simp_all +decide [ add_assoc ] ;
    cases min_cases idx ( List.length ( board.getStack sq ) ) <;> simp_all +decide;
    · cases h : mods[sq + outcome.value.toNat]?.getD Option.none <;> simp_all +decide;
      · grind;
      · linarith [ Nat.sub_add_cancel ‹_› ];
    · convert this using 1;
      cases mods[sq + outcome.value.toNat]?.getD Option.none <;> simp +decide [ * ]

set_option maxHeartbeats 4000000 in
theorem applyDie_preserves_boardSize
    (board : Board) (mods : Array (Option ModifierTile))
    (finished : List CamelColor) (outcome : DieOutcome)
    (h : board.size = numSquares) :
    (applyDie board mods finished outcome).1.size = numSquares := by
  have h_setStack_size : ∀ (b : Board) (sq : Nat) (s : Stack),
      (b.setStack sq s).size = b.size := setStack_size
  unfold CamelUp.applyDie; aesop

noncomputable section AristotleLemmas2

/-- Definition of the total count of a specific camel color on the board. -/
def totalCamelCount (b : Board) (c : CamelColor) : Nat :=
  (List.range numSquares).foldl (fun acc i => acc + (b.getStack i).count c) 0

/-- If `findCamelOnBoard` finds a camel at square `sq`, then `sq < numSquares`. -/
theorem findCamelOnBoard_bounds (b : Board) (c : CamelColor) (sq idx : Nat)
    (h : findCamelOnBoard b c = some (sq, idx)) : sq < numSquares := by
  have h_sq_valid : sq ∈ List.range numSquares := by
    have h_search : ∀ (squares : List Nat), findCamelOnBoard.searchSquares b c squares = Option.some (sq, idx) → sq ∈ squares := by
      intros squares hsquares
      induction' squares with squares_sq squares_sq ih generalizing sq idx
      all_goals generalize_proofs at *;
      · cases hsquares;
      · unfold findCamelOnBoard.searchSquares at hsquares; aesop;
    exact h_search _ h
  generalize_proofs at *; (
  exact List.mem_range.mp h_sq_valid |> Nat.lt_of_lt_of_le <| by decide;)

/-- Retrieving the stack at the index just set returns the new stack (index in bounds). -/
theorem getStack_setStack_eq (b : Board) (sq : Nat) (s : Stack) (h : sq < b.size) :
    (b.setStack sq s).getStack sq = s := by
  simp only [Board.getStack, Board.setStack] at *; simp [Array.getD];
  have h_setAt_sq : (Board.setStack.setAt s b.toList sq)[sq]?.getD [] = s := by
    have h_setAt_sq : ∀ (l : List Stack) (sq : Nat) (s : Stack), sq < l.length → (Board.setStack.setAt s l sq)[sq]?.getD [] = s := by
      intros l sq s h_sq_lt_l_len
      induction' l with l_head l_tail ih generalizing sq s
      all_goals generalize_proofs at *;
      · contradiction;
      · rcases sq with ( _ | sq ) <;> simp_all +arith +decide [ Board.setStack.setAt ];
    exact h_setAt_sq _ _ _ ( by simpa using h );
  aesop

/-- Setting a stack at `sq` does not change stacks at other squares. -/
theorem getStack_setStack_ne (b : Board) (sq i : Nat) (s : Stack) (h_ne : i ≠ sq) :
    (b.setStack sq s).getStack i = b.getStack i := by
  unfold Board.setStack Board.getStack;
  have h_setAt : ∀ (l : List Stack) (s : Stack) (sq : Nat) (i : Nat), i ≠ sq → (Board.setStack.setAt s l sq).getD i [] = l.getD i [] := by
    intros l s sq i hi;
    induction' l with l_head l_tail ih generalizing sq i;
    · exact?;
    · rcases sq with ( _ | sq ) <;> rcases i with ( _ | i ) <;> simp_all +decide [ Board.setStack.setAt ];
  aesop

/--
Updating a stack at `sq` changes the total camel count by `new_count - old_count`.
Expressed as an equality of sums to avoid subtraction issues.
-/
theorem totalCamelCount_setStack (b : Board) (sq : Nat) (s : Stack) (c : CamelColor)
    (h_size : b.size = numSquares) (h_sq : sq < numSquares) :
    totalCamelCount (b.setStack sq s) c + (b.getStack sq).count c =
    totalCamelCount b c + s.count c := by
  unfold totalCamelCount;
  have h_split : List.foldl (fun acc i => acc + List.count c ((b.setStack sq s).getStack i)) 0 (List.range CamelUp.numSquares) =
    List.foldl (fun acc i => acc + List.count c (b.getStack i)) 0 (List.range CamelUp.numSquares) +
    List.count c s - List.count c (b.getStack sq) := by
      have h_split : List.foldl (fun acc i => acc + List.count c ((b.setStack sq s).getStack i)) 0 (List.range CamelUp.numSquares) = ∑ i ∈ Finset.range CamelUp.numSquares, List.count c ((b.setStack sq s).getStack i) ∧ List.foldl (fun acc i => acc + List.count c (b.getStack i)) 0 (List.range CamelUp.numSquares) = ∑ i ∈ Finset.range CamelUp.numSquares, List.count c (b.getStack i) := by
        induction' CamelUp.numSquares with n ih <;> simp_all +decide [ Finset.sum_range_succ, List.range_succ ];
      rw [ h_split.left, h_split.right, tsub_eq_of_eq_add ];
      have h_split : ∑ i ∈ Finset.range CamelUp.numSquares, List.count c ((b.setStack sq s).getStack i) = ∑ i ∈ Finset.range CamelUp.numSquares, (if i = sq then List.count c s else List.count c (b.getStack i)) := by
        refine' Finset.sum_congr rfl fun i hi => _;
        split_ifs <;> simp_all +decide [ CamelUp.getStack_setStack_eq, CamelUp.getStack_setStack_ne ];
      simp_all +decide [ Finset.sum_ite, Finset.filter_eq', Finset.filter_ne' ];
      rw [ ← Finset.sum_erase_add _ _ ( Finset.mem_range.mpr h_sq ), add_comm ] ; ring;
  rw [ h_split, tsub_add_cancel_of_le ];
  refine' le_add_of_le_of_nonneg _ _;
  · have h_split : List.foldl (fun acc i => acc + List.count c (b.getStack i)) 0 (List.range CamelUp.numSquares) = List.sum (List.map (fun i => List.count c (b.getStack i)) (List.range CamelUp.numSquares)) := by
      rw [ List.sum_eq_foldl ];
      rw [ List.foldl_map ];
    exact h_split.symm ▸ List.le_sum_of_mem ( List.mem_map.mpr ⟨ sq, List.mem_range.mpr h_sq, rfl ⟩ );
  · exact Nat.zero_le _

end AristotleLemmas2

theorem applyDie_preserves_camelCount
    (board : Board) (mods : Array (Option ModifierTile))
    (finished : List CamelColor) (outcome : DieOutcome)
    (c : CamelColor) (h : board.size = numSquares) :
    let (board', finished', _) := applyDie board mods finished outcome
    finished'.count c +
    (List.range numSquares).foldl (fun acc i => acc + (board'.getStack i).count c) 0 =
    finished.count c +
    (List.range numSquares).foldl (fun acc i => acc + (board.getStack i).count c) 0 := by
  by_cases h_find : findCamelOnBoard board outcome.camel = none;
  · unfold CamelUp.applyDie; aesop;
  · obtain ⟨sq, idx, h_sq, h_idx⟩ : ∃ sq idx, findCamelOnBoard board outcome.camel = some (sq, idx) ∧ sq < numSquares := by
      obtain ⟨ sq, idx ⟩ := Option.ne_none_iff_exists'.mp h_find;
      exact ⟨ sq.1, sq.2, idx, by have := CamelUp.findCamelOnBoard_bounds board outcome.camel sq.1 sq.2 idx; aesop ⟩;
    unfold CamelUp.applyDie;
    simp [h_sq] at *;
    split_ifs <;> simp_all +decide [ List.count_append ];
    · have h_totalCamelCount_setStack : CamelUp.totalCamelCount (board.setStack sq (List.take idx (board.getStack sq))) c + (board.getStack sq).count c = CamelUp.totalCamelCount board c + (List.take idx (board.getStack sq)).count c := by
        apply CamelUp.totalCamelCount_setStack board sq (List.take idx (board.getStack sq)) c h h_idx;
      have h_count_split : (board.getStack sq).count c = (List.take idx (board.getStack sq)).count c + (List.drop idx (board.getStack sq)).count c := by
        rw [ ← List.count_append, List.take_append_drop ];
      linarith!;
    · cases mods[0]?.getD Option.none <;> simp_all +decide [ CamelUp.DieValue.toNat ];
    · unfold CamelUp.DieValue.toNat at * ; aesop ( simp_config := { decide := true } ) ;
    · have h_totalCamelCount_setStack : CamelUp.totalCamelCount (board.setStack sq (List.take idx (board.getStack sq))) c + (board.getStack sq).count c = CamelUp.totalCamelCount board c + (List.take idx (board.getStack sq)).count c := by
        apply CamelUp.totalCamelCount_setStack; assumption; assumption;
      generalize_proofs at *; (
      have h_totalCamelCount_setStack : (List.drop idx (board.getStack sq)).count c + (List.take idx (board.getStack sq)).count c = (board.getStack sq).count c := by
        rw [ add_comm, ← List.count_append, List.take_append_drop ]
      generalize_proofs at *; (
      linarith! [ CamelUp.totalCamelCount ( board.setStack sq ( List.take idx ( board.getStack sq ) ) ) c ] ;));
    · have h_totalCamelCount_setStack : ∀ (b : CamelUp.Board) (sq : Nat) (s : CamelUp.Stack) (c : CamelUp.CamelColor), b.size = CamelUp.numSquares → sq < CamelUp.numSquares → (List.foldl (fun acc i => acc + List.count c (CamelUp.Board.getStack (b.setStack sq s) i)) 0 (List.range CamelUp.numSquares)) + List.count c (CamelUp.Board.getStack b sq) = (List.foldl (fun acc i => acc + List.count c (CamelUp.Board.getStack b i)) 0 (List.range CamelUp.numSquares)) + List.count c s := by
        intros b sq s c hb hsq;
        convert CamelUp.totalCamelCount_setStack b sq s c hb hsq using 1;
      have h_totalCamelCount_setStack : (List.foldl (fun acc i => acc + List.count c (CamelUp.Board.getStack ((board.setStack sq (List.take idx (board.getStack sq))).setStack (match mods[sq + outcome.value.toNat]?.getD Option.none with | Option.none => (sq + outcome.value.toNat, Option.none) | Option.some tile => (if 0 < tile.effect then sq + outcome.value.toNat + 1 else sq + outcome.value.toNat - 1, Option.some tile.owner)).1 ((board.setStack sq (List.take idx (board.getStack sq))).getStack (match mods[sq + outcome.value.toNat]?.getD Option.none with | Option.none => (sq + outcome.value.toNat, Option.none) | Option.some tile => (if 0 < tile.effect then sq + outcome.value.toNat + 1 else sq + outcome.value.toNat - 1, Option.some tile.owner)).1 ++ List.drop idx (board.getStack sq))) i)) 0 (List.range CamelUp.numSquares)) + List.count c ((board.setStack sq (List.take idx (board.getStack sq))).getStack (match mods[sq + outcome.value.toNat]?.getD Option.none with | Option.none => (sq + outcome.value.toNat, Option.none) | Option.some tile => (if 0 < tile.effect then sq + outcome.value.toNat + 1 else sq + outcome.value.toNat - 1, Option.some tile.owner)).1) = (List.foldl (fun acc i => acc + List.count c (CamelUp.Board.getStack (board.setStack sq (List.take idx (board.getStack sq))) i)) 0 (List.range CamelUp.numSquares)) + List.count c ((board.setStack sq (List.take idx (board.getStack sq))).getStack (match mods[sq + outcome.value.toNat]?.getD Option.none with | Option.none => (sq + outcome.value.toNat, Option.none) | Option.some tile => (if 0 < tile.effect then sq + outcome.value.toNat + 1 else sq + outcome.value.toNat - 1, Option.some tile.owner)).1 ++ List.drop idx (board.getStack sq)) := by
          apply_assumption
          generalize_proofs at *; (
          rw [ ← h, CamelUp.setStack_size ]);
          assumption
      generalize_proofs at *; (
      cases h : mods[sq + outcome.value.toNat]?.getD Option.none <;> simp_all +decide [ List.count_append ] ; ring!;
      · have h_totalCamelCount_setStack : List.count c (List.take idx (board.getStack sq)) + List.count c (List.drop idx (board.getStack sq)) = List.count c (board.getStack sq) := by
          rw [ ← List.count_append, List.take_append_drop ]
        generalize_proofs at *; (
        grind);
      · have h_totalCamelCount_setStack : List.count c (List.take idx (board.getStack sq)) + List.count c (List.drop idx (board.getStack sq)) = List.count c (board.getStack sq) := by
          rw [ ← List.count_append, List.take_append_drop ]
        generalize_proofs at *; (
        grind +ring))

/-! ## step preserves ValidState (all move types) -/

/-! ### Bet-resolution size lemmas (needed below) -/

/-- `resolveLegBets` preserves scores array size. -/
theorem resolveLegBets_scores_size
    (scores : Array Int) (ranking : List CamelColor) (bets : List LegBetEntry) :
    (resolveLegBets scores ranking bets).size = scores.size := by
  unfold resolveLegBets
  induction bets generalizing scores with
  | nil => simp
  | cons bet rest ih =>
      simp only [List.foldl_cons]
      rw [ih]
      exact awardPlayer_size _ _ _

/-- `resolveRaceWinBets` preserves scores array size. -/
theorem resolveRaceWinBets_scores_size
    (scores : Array Int) (winner : CamelColor) (bets : List RaceBetEntry) :
    (resolveRaceWinBets scores winner bets).size = scores.size := by
  unfold resolveRaceWinBets
  have h : ∀ (bs : List RaceBetEntry) (sc : Array Int) (idx : Nat),
      (List.foldl (fun (pair : Array Int × Nat) (bet : RaceBetEntry) =>
        let (s, i) := pair
        if bet.camel == winner
        then (awardPlayer s bet.player (racePayoutAt i), i + 1)
        else (awardPlayer s bet.player (-1), i))
        (sc, idx) bs).1.size = sc.size := by
    intro bs
    induction bs with
    | nil => simp
    | cons bet rest ih =>
        intro sc idx
        simp only [List.foldl_cons]
        split_ifs <;> simp [awardPlayer_size, ih]
  exact h _ _ _

/-- `resolveRaceLoseBets` preserves scores array size. -/
theorem resolveRaceLoseBets_scores_size
    (scores : Array Int) (loser : CamelColor) (bets : List RaceBetEntry) :
    (resolveRaceLoseBets scores loser bets).size = scores.size :=
  resolveRaceWinBets_scores_size scores loser bets

noncomputable section AristotleLemmas3

/-- `advancePlayer` returns a value < n when n > 0. -/
theorem advancePlayer_lt (cur n : Nat) (h : n > 0) : advancePlayer cur n < n := by
  unfold CamelUp.advancePlayer
  split_ifs <;> [linarith; exact Nat.mod_lt _ h]

/-- Every colour appears at most once in `CamelColor.all`. -/
theorem CamelColor_all_count_le_one (c : CamelColor) : CamelColor.all.count c ≤ 1 := by
  rcases c with (_ | _ | _ | _ | _) <;> trivial

/-- Erasing from a bag that only holds valid colours preserves that property. -/
theorem bag_sub_erase (bag : List CamelColor) (c : CamelColor)
    (h : ∀ x ∈ bag, x ∈ CamelColor.all) : ∀ x ∈ bag.erase c, x ∈ CamelColor.all :=
  fun x hx => h x (List.mem_of_mem_erase hx)

/-- Erasing from a bag where each colour appears ≤ 1 time preserves that property. -/
theorem bag_each_once_erase (bag : List CamelColor) (c : CamelColor)
    (h : ∀ x, bag.count x ≤ 1) : ∀ x, (bag.erase c).count x ≤ 1 := by
  intro x
  -- List.erase_sublist : bag.erase c <+ bag  (implicit args inferred)
  -- List.Sublist.count_le (a) (h : l₁ <+ l₂) : l₁.count a ≤ l₂.count a
  exact Nat.le_trans (List.erase_sublist.count_le x) (h x)

/-- Roll preserves board size. -/
theorem step_roll_preserves_board_size (gs : GameState) (outcome : DieOutcome)
    (gs' : GameState) (h_valid : ValidState gs)
    (h_step : step gs (Move.Roll outcome) = some gs') : gs'.board.size = numSquares := by
  have h := applyDie_preserves_boardSize gs.board gs.modifiers gs.finishedCamels outcome
                h_valid.board_size
  unfold CamelUp.step at h_step; aesop

/-- Roll preserves camel uniqueness. -/
theorem step_roll_preserves_camel_unique (gs : GameState) (outcome : DieOutcome)
    (gs' : GameState) (h_valid : ValidState gs)
    (h_step : step gs (Move.Roll outcome) = some gs') :
    ∀ c : CamelColor,
      gs'.finishedCamels.count c +
      (List.range numSquares).foldl (fun acc i => acc + (gs'.board.getStack i).count c) 0 = 1 := by
  intro c
  convert applyDie_preserves_camelCount gs.board gs.modifiers gs.finishedCamels outcome c
              h_valid.board_size using 1
  · unfold CamelUp.step at h_step; aesop
  · rw [← h_valid.camel_unique c]

end AristotleLemmas3

/-! ## AristotleLemmas4: Roll branch field lemmas (from batch f92d8fc5) -/
section AristotleLemmas4

/-- Roll: all remaining dice are valid CamelColors. -/
theorem step_Roll_bag_sub (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (_h_valid : ValidState gs)
    (_h_step  : step gs (Move.Roll outcome) = some gs') :
    ∀ c ∈ gs'.diceBag, c ∈ CamelColor.all := fun c _ => by
  cases c <;> simp [CamelColor.all]

-- For Roll proofs: unfold step, split outer/contains guards (hgo, hcontains) →
-- 3 goals: 2 closed by simp (none=some); 1 success with h_step as conjunction.
-- Then obtain strips the conjunction, inner split_ifs gives the 3 Roll arms,
-- and simp+subst resolves each arm.

/-- Roll: no color appears twice in the remaining dice bag. -/
theorem step_Roll_bag_each_once (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.Roll outcome) = some gs') :
    ∀ c : CamelColor, gs'.diceBag.count c ≤ 1 := by
  sorry

/-- Roll: scores array size is preserved. -/
theorem step_Roll_scores_size (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.Roll outcome) = some gs') :
    gs'.scores.size = gs'.numPlayers := by
  sorry

/-- Roll: legBetTiles array still has 5 entries. -/
theorem step_Roll_tiles_size (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.Roll outcome) = some gs') :
    gs'.legBetTiles.size = 5 := by
  sorry

/-- Roll: modifiers array size is preserved. -/
theorem step_Roll_mods_size (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.Roll outcome) = some gs') :
    gs'.modifiers.size = numSquares := by
  convert h_valid.mods_size using 1
  unfold CamelUp.step at h_step; aesop

/-- Roll: currentPlayer stays within [0, numPlayers). -/
theorem step_Roll_player_valid (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.Roll outcome) = some gs') :
    gs'.numPlayers > 0 → gs'.currentPlayer < gs'.numPlayers := by
  sorry

end AristotleLemmas4

/-- The central safety property: every legal step preserves all ValidState invariants.
    Non-Roll branches: proved in batch 6adf4117.
    Roll branch: board_size + camel_unique proved; 5 field lemmas sorry-stubbed for next Aristotle batch. -/
theorem step_preserves_valid
    (gs : GameState) (move : Move) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs move = some gs') :
    ValidState gs' := by
  match move with
  | .Roll outcome => exact {
      board_size    := step_roll_preserves_board_size   gs outcome gs' h_valid h_step
      camel_unique  := step_roll_preserves_camel_unique gs outcome gs' h_valid h_step
      bag_sub       := step_Roll_bag_sub       gs outcome gs' h_valid h_step
      bag_each_once := step_Roll_bag_each_once gs outcome gs' h_valid h_step
      scores_size   := step_Roll_scores_size   gs outcome gs' h_valid h_step
      tiles_size    := step_Roll_tiles_size    gs outcome gs' h_valid h_step
      player_valid  := step_Roll_player_valid  gs outcome gs' h_valid h_step
      mods_size     := step_Roll_mods_size     gs outcome gs' h_valid h_step }
  | .BetRaceWin c =>
      -- Since step = some _, gameOver must be false; then the match arm reduces by rfl
      have hno : gs.gameOver = false := by
        rcases Bool.eq_false_or_eq_true gs.gameOver with h | h
        · simp [step, h] at h_step
        · exact h
      simp only [step, hno, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h_step
      subst h_step
      exact {
        board_size    := h_valid.board_size
        camel_unique  := h_valid.camel_unique
        bag_sub       := h_valid.bag_sub
        bag_each_once := h_valid.bag_each_once
        scores_size   := h_valid.scores_size
        tiles_size    := h_valid.tiles_size
        player_valid  := fun hn => advancePlayer_lt gs.currentPlayer gs.numPlayers hn
        mods_size     := h_valid.mods_size }
  | .BetRaceLose c =>
      have hno : gs.gameOver = false := by
        rcases Bool.eq_false_or_eq_true gs.gameOver with h | h
        · simp [step, h] at h_step
        · exact h
      simp only [step, hno, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h_step
      subst h_step
      exact {
        board_size    := h_valid.board_size
        camel_unique  := h_valid.camel_unique
        bag_sub       := h_valid.bag_sub
        bag_each_once := h_valid.bag_each_once
        scores_size   := h_valid.scores_size
        tiles_size    := h_valid.tiles_size
        player_valid  := fun hn => advancePlayer_lt gs.currentPlayer gs.numPlayers hn
        mods_size     := h_valid.mods_size }
  | .BetLeg c =>
      have hno : gs.gameOver = false := by
        rcases Bool.eq_false_or_eq_true gs.gameOver with h | h
        · simp [step, h] at h_step
        · exact h
      simp only [step, hno, Bool.false_eq_true, ↓reduceIte] at h_step
      split at h_step
      · simp at h_step
      · rename_i tileVal rest
        simp only [Option.some.injEq] at h_step
        subst h_step
        exact {
          board_size    := h_valid.board_size
          camel_unique  := h_valid.camel_unique
          bag_sub       := h_valid.bag_sub
          bag_each_once := h_valid.bag_each_once
          scores_size   := h_valid.scores_size
          tiles_size    := by simp [updateArr_size, h_valid.tiles_size]
          player_valid  := fun hn => advancePlayer_lt gs.currentPlayer gs.numPlayers hn
          mods_size     := h_valid.mods_size }
  | .PlaceTile sq pos =>
      have hno : gs.gameOver = false := by
        rcases Bool.eq_false_or_eq_true gs.gameOver with h | h
        · simp [step, h] at h_step
        · exact h
      -- Reduce the step body (outer gameOver guard already eliminated)
      simp only [step, hno, Bool.false_eq_true, ↓reduceIte] at h_step
      -- split_ifs on h_step: 4 none-guards + 2 pos branches (success)
      -- We close none-branches with simp and success branches with subst+exact
      split_ifs at h_step with h1 h2 h3 h4 h5
      all_goals simp_all only [Option.some.injEq]
      all_goals try subst h_step
      all_goals try exact {
        board_size    := h_valid.board_size
        camel_unique  := h_valid.camel_unique
        bag_sub       := h_valid.bag_sub
        bag_each_once := h_valid.bag_each_once
        scores_size   := h_valid.scores_size
        tiles_size    := h_valid.tiles_size
        player_valid  := fun hn => advancePlayer_lt gs.currentPlayer gs.numPlayers hn
        mods_size     := by simp [updateArr_size, h_valid.mods_size] }

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
