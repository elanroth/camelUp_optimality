/-
  HELPER LEMMAS FILE — for Aristotle (4th batch)
  ================================================

  TASK: Replace every `sorry` in this file with a real proof.
  The main theorem `step_preserves_valid` is already assembled in
  CamelUp/Proofs/Invariants.lean using these helpers — just fill them in here.

  ── CRITICAL BUG FIX FROM LAST BATCH ──────────────────────────────────────────
  In the previous Aristotle run (3ccc4914) almost every lemma failed with:
    "Function expected at `updateArr`" / "Function expected at `step`" /
    "Function expected at `ValidState`"
  This was caused by `updateArr` being `private` in CamelUp.Model.Step.
  DO NOT reference `updateArr` by name anywhere in this file.
  Instead use `updateArr_size` (the public theorem exported from Step.lean).

  Other env notes:
    • `step   : GameState → Move → Option GameState`  (use `simp only [step] at h_step`
      or `unfold step at h_step` to unfold it)
    • `ValidState` is a *structure* with fields accessed as `h_valid.board_size`,
      `h_valid.camel_unique`, `h_valid.bag_sub`, `h_valid.bag_each_once`,
      `h_valid.scores_size`, `h_valid.tiles_size`, `h_valid.player_valid`,
      `h_valid.mods_size`
    • `GameState` fields: `board`, `finishedCamels`, `diceBag`, `modifiers`,
      `legBetTiles`, `scores`, `numPlayers`, `currentPlayer`
    • `numSquares : Nat` is a constant (= 16)

  ── PRIORITY ORDER (easiest first) ────────────────────────────────────────────
  1. BetLeg helpers (tiles_size, scores_size, player_valid):
       BetLeg only (a) calls `updateArr gs.legBetTiles idx rest` on legBetTiles
       and (b) advances the player. Everything else is unchanged.
       For tiles_size: use `updateArr_size` + `h_valid.tiles_size`.
       For scores_size: scores are untouched, numPlayers unchanged, use `h_valid.scores_size`.
       For player_valid: `gs'.currentPlayer = advancePlayer gs.currentPlayer gs.numPlayers`;
         use `advancePlayer_bound` (proved below).

  2. BetRaceWin / BetRaceLose helpers (fields_unchanged, player_valid × 2):
       These branches only append one entry to `raceWinBets` / `raceLoseBets` and
       advance the player. Board, bag, scores, tiles, modifiers are all untouched.
       `unfold step at h_step; split_ifs at h_step; simp_all` should expose the
       field equalities.

  3. PlaceTile helpers (board_unchanged, mods_size, player_valid):
       PlaceTile only writes `updateArr gs.modifiers sq tile` — all other fields
       unchanged. For mods_size: `updateArr_size` + `h_valid.mods_size`.

  4. Roll helpers (hardest — last):
       Roll calls `applyDie` then conditionally `resolveLegBets`.
       Use already-proved lemmas:
         • `applyDie_preserves_boardSize`  → board_size
         • `applyDie_preserves_camelCount` → camel_unique (each colour count preserved)
         • `resolveLegBets_scores_size`    → scores_size
         • `h_valid.bag_each_once` + List.count_erase_le_one' → bag_each_once
         • `h_valid.bag_sub` + List.mem_erase_sub' → bag_sub
       The diceBag after Roll is either `gs.diceBag.erase outcome.camel`
       (mid-leg) or `CamelColor.all` (leg end, when bag becomes empty).
       `CamelColor.all` is a literal list of all five colours — membership and
       count-≤-1 both hold by `decide`.

  ── ALREADY PROVED (do not re-prove) ─────────────────────────────────────────
  From CamelUp/Proofs/Invariants.lean (available via import):
    • applyDie_preserves_boardSize, applyDie_preserves_totalCount,
      applyDie_preserves_camelCount
    • resolveLegBets_scores_size, resolveRaceWinBets_scores_size
    • setStack_size, totalCamelCount_setStack

  From CamelUp/Model/Step.lean (available via import):
    • updateArr_size   : (updateArr arr i v).size = arr.size
    • awardPlayer_size : (awardPlayer scores p delta).size = scores.size

  Proved in this file (keep these, use them in Roll helpers):
    • advancePlayer_bound
    • List.mem_erase_sub', List.count_erase_le', List.count_erase_le_one'
-/
import Mathlib
import CamelUp.Model.Types
import CamelUp.Model.Step

namespace CamelUp

open CamelUp

/-! ## Utility: advancePlayer stays in bounds -/

/-- `advancePlayer` always produces a valid player index. -/
theorem advancePlayer_bound (cur n : Nat) (h : 0 < n) :
    advancePlayer cur n < n := by
  unfold advancePlayer
  simp [Nat.pos_iff_ne_zero.mp h]
  exact Nat.mod_lt _ h

/-! ## Utility: List.erase preserves invariants needed for diceBag -/

/-- Every element remaining after erase was in the original list. -/
theorem List.mem_erase_sub {α} [BEq α] [LawfulBEq α] (l : List α) (a : α) :
    ∀ x ∈ l.erase a, x ∈ l := by
  intro x hx
  exact List.mem_of_mem_erase hx

/-- Erasing an element cannot increase count of any element. -/
theorem List.count_erase_le {α} [BEq α] [LawfulBEq α] (l : List α) (a b : α) :
    (l.erase a).count b ≤ l.count b := by
  induction l with
  | nil => simp
  | cons h t ih =>
      simp [List.erase]
      split_ifs with heq
      · simp [List.count_cons]
        omega
      · simp [List.count_cons]
        omega

/-- If `a` appears at most once in `l`, it appears at most once after erase. -/
theorem List.count_erase_le_one {α} [BEq α] [LawfulBEq α] (l : List α) (a b : α)
    (h : l.count b ≤ 1) : (l.erase a).count b ≤ 1 :=
  Nat.le_trans (List.count_erase_le l a b) h

/-! ## Roll branch: field-by-field preservation -/

/-- After a legal Roll, the board size is still numSquares. -/
theorem step_Roll_board_size (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.Roll outcome) = some gs') :
    gs'.board.size = numSquares := by
  sorry

/-- After a legal Roll, every colour appears exactly once across board + finished. -/
theorem step_Roll_camel_unique (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.Roll outcome) = some gs') :
    ∀ c : CamelColor,
      gs'.finishedCamels.count c +
      (List.range numSquares).foldl (fun acc i => acc + (gs'.board.getStack i).count c) 0 = 1 := by
  sorry

/-- After a legal Roll, the remaining dice bag entries are all valid colours. -/
theorem step_Roll_bag_sub (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.Roll outcome) = some gs') :
    ∀ c ∈ gs'.diceBag, c ∈ CamelColor.all := by
  intro c hc
  -- gs'.diceBag = gs.diceBag.erase outcome.camel (mid-leg) or CamelColor.all (leg end)
  -- Both are subsets of CamelColor.all.
  sorry

/-- After a legal Roll, no colour appears twice in the remaining bag. -/
theorem step_Roll_bag_each_once (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.Roll outcome) = some gs') :
    ∀ c : CamelColor, gs'.diceBag.count c ≤ 1 := by
  sorry

/-- After a legal Roll, the scores array length is preserved. -/
theorem step_Roll_scores_size (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.Roll outcome) = some gs') :
    gs'.scores.size = gs'.numPlayers := by
  -- numPlayers is invariant; scores grow only via awardPlayer/resolveLegBets/etc.,
  -- all of which preserve size by awardPlayer_size / resolveLegBets_scores_size.
  sorry

/-- After a legal Roll, legBetTiles still has 5 entries. -/
theorem step_Roll_tiles_size (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.Roll outcome) = some gs') :
    gs'.legBetTiles.size = 5 := by
  sorry

/-- After a legal Roll, modifiers array size is still numSquares. -/
theorem step_Roll_mods_size (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.Roll outcome) = some gs') :
    gs'.modifiers.size = numSquares := by
  sorry

/-- After a legal Roll, currentPlayer is in range. -/
theorem step_Roll_player_valid (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.Roll outcome) = some gs') :
    gs'.numPlayers > 0 → gs'.currentPlayer < gs'.numPlayers := by
  intro hn
  -- gs'.currentPlayer = advancePlayer gs.currentPlayer gs.numPlayers
  -- advancePlayer_bound gives the result.
  sorry

/-! ## BetLeg branch -/

/-- BetLeg does not touch the board, finished camels, bag, or modifiers. -/
theorem step_BetLeg_board_unchanged (gs : GameState) (c : CamelColor) (gs' : GameState)
    (h_step : step gs (Move.BetLeg c) = some gs') :
    gs'.board = gs.board ∧ gs'.finishedCamels = gs.finishedCamels ∧
    gs'.diceBag = gs.diceBag ∧ gs'.modifiers = gs.modifiers := by
  unfold step at h_step
  simp at h_step
  split_ifs at h_step with hgo htiles <;> simp_all
  · cases htiles
  · obtain ⟨_, rfl⟩ := Option.some.inj h_step
    simp

/-- After a legal BetLeg, legBetTiles still has 5 entries
    (updateArr does not change array size). -/
theorem step_BetLeg_tiles_size (gs : GameState) (c : CamelColor) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.BetLeg c) = some gs') :
    gs'.legBetTiles.size = 5 := by
  sorry

/-- After a legal BetLeg, scores size is preserved (scores untouched). -/
theorem step_BetLeg_scores_size (gs : GameState) (c : CamelColor) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.BetLeg c) = some gs') :
    gs'.scores.size = gs'.numPlayers := by
  sorry

/-- After a legal BetLeg, currentPlayer is in range. -/
theorem step_BetLeg_player_valid (gs : GameState) (c : CamelColor) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.BetLeg c) = some gs') :
    gs'.numPlayers > 0 → gs'.currentPlayer < gs'.numPlayers := by
  sorry

/-! ## BetRaceWin / BetRaceLose branches (symmetric) -/

/-- BetRaceWin / BetRaceLose only append to the bet lists; all other fields unchanged. -/
theorem step_BetRace_fields_unchanged (gs : GameState) (move : Move) (gs' : GameState)
    (h_move : move = Move.BetRaceWin move.1 ∨ move = Move.BetRaceLose move.1)
    (h_step : step gs move = some gs') :
    gs'.board = gs.board ∧ gs'.finishedCamels = gs.finishedCamels ∧
    gs'.diceBag = gs.diceBag ∧ gs'.modifiers = gs.modifiers ∧
    gs'.scores = gs.scores ∧ gs'.legBetTiles = gs.legBetTiles := by
  sorry

/-- After BetRaceWin, currentPlayer is in range. -/
theorem step_BetRaceWin_player_valid (gs : GameState) (c : CamelColor) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.BetRaceWin c) = some gs') :
    gs'.numPlayers > 0 → gs'.currentPlayer < gs'.numPlayers := by
  sorry

/-- After BetRaceLose, currentPlayer is in range. -/
theorem step_BetRaceLose_player_valid (gs : GameState) (c : CamelColor) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.BetRaceLose c) = some gs') :
    gs'.numPlayers > 0 → gs'.currentPlayer < gs'.numPlayers := by
  sorry

/-! ## PlaceTile branch -/

/-- PlaceTile does not change the board stacks only the modifiers array. -/
theorem step_PlaceTile_board_unchanged (gs : GameState) (sq : Nat) (pos : Bool) (gs' : GameState)
    (h_step : step gs (Move.PlaceTile sq pos) = some gs') :
    gs'.board = gs.board ∧ gs'.finishedCamels = gs.finishedCamels ∧
    gs'.diceBag = gs.diceBag ∧ gs'.scores = gs.scores ∧
    gs'.legBetTiles = gs.legBetTiles := by
  sorry

/-- After PlaceTile, modifiers array has size numSquares (updateArr preserves size). -/
theorem step_PlaceTile_mods_size (gs : GameState) (sq : Nat) (pos : Bool) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.PlaceTile sq pos) = some gs') :
    gs'.modifiers.size = numSquares := by
  sorry

/-- After PlaceTile, currentPlayer is in range. -/
theorem step_PlaceTile_player_valid (gs : GameState) (sq : Nat) (pos : Bool) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.PlaceTile sq pos) = some gs') :
    gs'.numPlayers > 0 → gs'.currentPlayer < gs'.numPlayers := by
  sorry

/-! ## Main theorem — uses all helpers above -/

/-- Every legal step preserves all ValidState invariants. -/
theorem step_preserves_valid
    (gs : GameState) (move : Move) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs move = some gs') :
    ValidState gs' := by
  -- Case split on the move type, then apply per-field helpers.
  match move with
  | .Roll outcome => exact {
      board_size   := step_Roll_board_size   gs outcome gs' h_valid h_step
      camel_unique := step_Roll_camel_unique gs outcome gs' h_valid h_step
      bag_sub      := step_Roll_bag_sub      gs outcome gs' h_valid h_step
      bag_each_once:= step_Roll_bag_each_once gs outcome gs' h_valid h_step
      scores_size  := step_Roll_scores_size  gs outcome gs' h_valid h_step
      tiles_size   := step_Roll_tiles_size   gs outcome gs' h_valid h_step
      player_valid := step_Roll_player_valid gs outcome gs' h_valid h_step
      mods_size    := step_Roll_mods_size    gs outcome gs' h_valid h_step }
  | .BetLeg c => exact {
      board_size   := by have := step_BetLeg_board_unchanged gs c gs' h_step; simp [this.1, h_valid.board_size]
      camel_unique := by have := step_BetLeg_board_unchanged gs c gs' h_step; simp [this.1, this.2.1]; exact h_valid.camel_unique
      bag_sub      := by have := step_BetLeg_board_unchanged gs c gs' h_step; simp [this.2.2.1]; exact h_valid.bag_sub
      bag_each_once:= by have := step_BetLeg_board_unchanged gs c gs' h_step; simp [this.2.2.1]; exact h_valid.bag_each_once
      scores_size  := step_BetLeg_scores_size gs c gs' h_valid h_step
      tiles_size   := step_BetLeg_tiles_size  gs c gs' h_valid h_step
      player_valid := step_BetLeg_player_valid gs c gs' h_valid h_step
      mods_size    := by have := step_BetLeg_board_unchanged gs c gs' h_step; simp [this.2.2.2]; exact h_valid.mods_size }
  | .BetRaceWin c => exact {
      board_size   := by simp [step] at h_step; simp_all; exact h_valid.board_size
      camel_unique := by simp [step] at h_step; simp_all; exact h_valid.camel_unique
      bag_sub      := by simp [step] at h_step; simp_all; exact h_valid.bag_sub
      bag_each_once:= by simp [step] at h_step; simp_all; exact h_valid.bag_each_once
      scores_size  := by simp [step] at h_step; simp_all; exact h_valid.scores_size
      tiles_size   := by simp [step] at h_step; simp_all; exact h_valid.tiles_size
      player_valid := step_BetRaceWin_player_valid gs c gs' h_valid h_step
      mods_size    := by simp [step] at h_step; simp_all; exact h_valid.mods_size }
  | .BetRaceLose c => exact {
      board_size   := by simp [step] at h_step; simp_all; exact h_valid.board_size
      camel_unique := by simp [step] at h_step; simp_all; exact h_valid.camel_unique
      bag_sub      := by simp [step] at h_step; simp_all; exact h_valid.bag_sub
      bag_each_once:= by simp [step] at h_step; simp_all; exact h_valid.bag_each_once
      scores_size  := by simp [step] at h_step; simp_all; exact h_valid.scores_size
      tiles_size   := by simp [step] at h_step; simp_all; exact h_valid.tiles_size
      player_valid := step_BetRaceLose_player_valid gs c gs' h_valid h_step
      mods_size    := by simp [step] at h_step; simp_all; exact h_valid.mods_size }
  | .PlaceTile sq pos => exact {
      board_size   := by have := step_PlaceTile_board_unchanged gs sq pos gs' h_step; simp [this.1, h_valid.board_size]
      camel_unique := by have := step_PlaceTile_board_unchanged gs sq pos gs' h_step; simp [this.1, this.2.1]; exact h_valid.camel_unique
      bag_sub      := by have := step_PlaceTile_board_unchanged gs sq pos gs' h_step; simp [this.2.2.1]; exact h_valid.bag_sub
      bag_each_once:= by have := step_PlaceTile_board_unchanged gs sq pos gs' h_step; simp [this.2.2.1]; exact h_valid.bag_each_once
      scores_size  := by have := step_PlaceTile_board_unchanged gs sq pos gs' h_step; simp [this.2.2.2.1]; exact h_valid.scores_size
      tiles_size   := by have := step_PlaceTile_board_unchanged gs sq pos gs' h_step; simp [this.2.2.2.2]; exact h_valid.tiles_size
      player_valid := step_PlaceTile_player_valid gs sq pos gs' h_valid h_step
      mods_size    := step_PlaceTile_mods_size gs sq pos gs' h_valid h_step }

end CamelUp
