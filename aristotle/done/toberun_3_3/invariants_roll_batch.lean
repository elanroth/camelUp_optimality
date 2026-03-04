-- Aristotle Batch 3/3: CamelUp.Proofs.Invariants — Roll branch field lemmas
--
-- Batch 95717055 proved:
--   ✅ step_Roll_mods_size   (convert h_valid.mods_size using 1; unfold step; aesop)
-- Still sorry (this batch targets):
--   • step_Roll_bag_each_once
--   • step_Roll_scores_size
--   • step_Roll_tiles_size
--   • step_Roll_player_valid  (95717055 left `exact?` — not a real proof)
--
-- The step function for Roll (after `unfold CamelUp.step`):
--
--   if gs.gameOver then none
--   else
--     if !gs.diceBag.contains outcome.camel then none
--     else
--       let scores₁   := awardPlayer gs.scores gs.currentPlayer 1
--       let newBag     := gs.diceBag.erase outcome.camel
--       let (newBoard, newFinished, mTileOwner) :=
--             applyDie gs.board gs.modifiers gs.finishedCamels outcome
--       let scores₂    := match mTileOwner with
--                         | none   => scores₁
--                         | some p => awardPlayer scores₁ p 1
--       if !newFinished.isEmpty then
--         some { board:=newBoard, diceBag:=[],              gameOver:=true,
--                scores:=resolveLegBets(resolveRaceWinBets(resolveRaceLoseBets scores₂ ..)) ..}
--       else if newBag.isEmpty then
--         some { board:=newBoard, diceBag:=CamelColor.all,  legNo:=gs.legNo+1,
--                scores:=resolveLegBets scores₂ .., legBetTiles:=initialLegBetTiles .. }
--       else
--         some { board:=newBoard, diceBag:=newBag,
--                scores:=scores₂ .. }
--
-- Three Roll arms:
--   Arm A (race over):  gameOver:=true,  diceBag:=[]
--   Arm B (leg end):    gameOver:=false, diceBag:=CamelColor.all, legNo+=1, legBetTiles reset
--   Arm C (mid-leg):    gameOver:=false, diceBag:=gs.diceBag.erase outcome.camel
--
-- Supporting lemmas already proved in Invariants.lean (use freely):
--   bag_each_once_erase (c : CamelColor) (bag : List CamelColor)
--     (h : ∀ x, bag.count x ≤ 1) : ∀ x, (bag.erase c).count x ≤ 1
--   resolveLegBets_scores_size, resolveRaceWinBets_scores_size,
--   resolveRaceLoseBets_scores_size : all preserve scores.size
--   awardPlayer_size : awardPlayer preserves scores.size
--   advancePlayer_lt (p n : Nat) (h : n > 0) : advancePlayer p n < n
--
-- Tactic notes:
--   After `simp only [Option.some.injEq] at h_step; subst h_step`, gs' is replaced
--   by the concrete record literal, and goals become directly provable.
--   For the three-arm split, a useful approach:
--     `unfold CamelUp.step at h_step`
--     then `simp only [Bool.not_eq_true] at h_step` or similar to normalise,
--     then `rcases` / `split_ifs` to case-split on the three outcomes.

import CamelUp.Model.Types
import CamelUp.Model.Step
import CamelUp.Controller.Sim
import CamelUp.Controller.EV
import CamelUp.Controller.Policy
import CamelUp.Proofs.Invariants

namespace CamelUp.Invariants.RollBatch

open CamelUp CamelUp.Sim CamelUp.EV CamelUp.Policy

/-! ## Small helpers for Roll proofs -/

lemma initialLegBetTiles_size : initialLegBetTiles.size = 5 := by
  simp [initialLegBetTiles]

lemma scores_size_after_tile (scores : Array Int) (mTileOwner : Option Nat) :
    (match mTileOwner with
      | none => scores
      | some p => awardPlayer scores p 1).size = scores.size := by
  cases mTileOwner <;> simp [awardPlayer_size]

lemma scores_size_after_leg (scores : Array Int) (ranking : List CamelColor)
    (bets : List LegBetEntry) :
    (resolveLegBets scores ranking bets).size = scores.size := by
  simp [resolveLegBets_scores_size]

lemma scores_size_after_leg_race (scores : Array Int) (ranking : List CamelColor)
    (winner loser : CamelColor) (legBets : List LegBetEntry)
    (winBets loseBets : List RaceBetEntry) :
    (resolveRaceLoseBets
        (resolveRaceWinBets (resolveLegBets scores ranking legBets) winner winBets)
        loser loseBets).size = scores.size := by
  simp [resolveRaceLoseBets_scores_size, resolveRaceWinBets_scores_size, resolveLegBets_scores_size]

lemma roll_step_guards (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (h_step : CamelUp.step gs (Move.Roll outcome) = some gs') :
    gs.gameOver = false ∧ gs.diceBag.contains outcome.camel = true := by
  cases hgo : gs.gameOver with
  | true =>
      simp [CamelUp.step, hgo] at h_step
  | false =>
      cases hcontains : gs.diceBag.contains outcome.camel with
      | true =>
          aesop
      | false =>
          simp [CamelUp.step, hgo, hcontains] at h_step

lemma roll_step_simp (gs : GameState) (outcome : DieOutcome)
    (hgo : gs.gameOver = false)
    (hcontains : gs.diceBag.contains outcome.camel = true) :
    CamelUp.step gs (Move.Roll outcome) =
      let scores₁ := awardPlayer gs.scores gs.currentPlayer 1
      let newBag := gs.diceBag.erase outcome.camel
      let (newBoard, newFinished, mTileOwner) :=
        applyDie gs.board gs.modifiers gs.finishedCamels outcome
      let scores₂ := match mTileOwner with
        | none => scores₁
        | some p => awardPlayer scores₁ p 1
      let nextPlayer := advancePlayer gs.currentPlayer gs.numPlayers
      let ranking := legRanking newBoard newFinished
      if !newFinished.isEmpty then
        let winner := newFinished.head?.getD .White
        let loser := ranking.getLast?.getD .Blue
        let scores₃ := resolveLegBets scores₂ ranking gs.legBetsPlaced
        let scores₄ := resolveRaceWinBets scores₃ winner gs.raceBetsWin
        let scores₅ := resolveRaceLoseBets scores₄ loser gs.raceBetsLose
        some { gs with board := newBoard
                       diceBag := []
                       finishedCamels := newFinished
                       currentPlayer := nextPlayer
                       scores := scores₅
                       legBetsPlaced := []
                       gameOver := true }
      else if newBag.isEmpty then
        let scores₃ := resolveLegBets scores₂ ranking gs.legBetsPlaced
        some { gs with board := newBoard
                       diceBag := CamelColor.all
                       legNo := gs.legNo + 1
                       finishedCamels := newFinished
                       currentPlayer := nextPlayer
                       scores := scores₃
                       legBetTiles := initialLegBetTiles
                       legBetsPlaced := [] }
      else
        some { gs with board := newBoard
                       diceBag := newBag
                       finishedCamels := newFinished
                       currentPlayer := nextPlayer
                       scores := scores₂ } := by
  unfold CamelUp.step
  simp [hgo, hcontains]
  sorry








lemma erase_stay_under : ∀ (c : CamelColor) (gs : GameState) (outcome : DieOutcome), ValidState gs → List.count c (gs.diceBag.erase outcome.camel) ≤ 1 := by
  sorry







/-- Roll: no color appears twice in the remaining dice bag.
    Arm A (race over, diceBag=[]): count=0 ≤ 1 by simp
    Arm B (leg end, diceBag=CamelColor.all): count ≤ 1 by `cases c <;> decide`
    Arm C (mid-leg, diceBag=erase): use bag_each_once_erase + h_valid.bag_each_once -/
theorem step_Roll_bag_each_once (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : CamelUp.step gs (Move.Roll outcome) = some gs') :
    ∀ c : CamelColor, gs'.diceBag.count c ≤ 1 := by
  have ⟨hgo, hcontains⟩ := roll_step_guards gs outcome gs' h_step
  have h_step' := h_step
  simp [roll_step_simp gs outcome hgo hcontains] at h_step'
  intro c
  split_ifs at h_step'
  all_goals
    simp [Option.some.injEq] at h_step'
    subst h_step'
    simp
  try
    cases c <;> aesop
  apply erase_stay_under _ _ _ h_valid





/-- Roll: scores array size is preserved.
    Arm A: size = resolveRaceLoseBets(resolveRaceWinBets(resolveLegBets(awardPlayer ...))).size
           = gs.numPlayers by the *_scores_size lemmas + awardPlayer_size + h_valid.scores_size
    Arm B: size = resolveLegBets(awardPlayer ...).size = gs.numPlayers
    Arm C: size = (match mTileOwner with | none => awardPlayer .. | some p => awardPlayer(awardPlayer ..)).size
           = gs.numPlayers by awardPlayer_size + h_valid.scores_size -/
theorem step_Roll_scores_size (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : CamelUp.step gs (Move.Roll outcome) = some gs') :
    gs'.scores.size = gs'.numPlayers := by
  have ⟨hgo, hcontains⟩ := roll_step_guards gs outcome gs' h_step
  have h_step' := h_step
  simp [roll_step_simp gs outcome hgo hcontains] at h_step'
  split_ifs at h_step'
  all_goals
    simp [Option.some.injEq] at h_step'
    subst h_step'
    simp [scores_size_after_leg_race, scores_size_after_leg, scores_size_after_tile,
      awardPlayer_size, h_valid.scores_size]

/-- Roll: legBetTiles array still has 5 entries.
    Arm A: legBetTiles = gs.legBetTiles → exact h_valid.tiles_size
    Arm B: legBetTiles = initialLegBetTiles → decide  (CamelColor has 5 constructors)
    Arm C: legBetTiles = gs.legBetTiles → exact h_valid.tiles_size -/
theorem step_Roll_tiles_size (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : CamelUp.step gs (Move.Roll outcome) = some gs') :
    gs'.legBetTiles.size = 5 := by
  have ⟨hgo, hcontains⟩ := roll_step_guards gs outcome gs' h_step
  have h_step' := h_step
  simp [roll_step_simp gs outcome hgo hcontains] at h_step'
  split_ifs at h_step'
  all_goals
    simp [Option.some.injEq] at h_step'
    subst h_step'
    simp [h_valid.tiles_size, initialLegBetTiles_size]

-- step_Roll_mods_size: proved by batch 95717055
--   convert h_valid.mods_size using 1; unfold CamelUp.step at h_step; aesop

/-- Roll: currentPlayer advances correctly and stays in-bounds.
    All arms set currentPlayer := advancePlayer gs.currentPlayer gs.numPlayers
    → exact advancePlayer_lt gs.currentPlayer gs.numPlayers hn -/
theorem step_Roll_player_valid (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : CamelUp.step gs (Move.Roll outcome) = some gs') :
    gs'.numPlayers > 0 → gs'.currentPlayer < gs'.numPlayers := by
  have ⟨hgo, hcontains⟩ := roll_step_guards gs outcome gs' h_step
  have h_step' := h_step
  simp [roll_step_simp gs outcome hgo hcontains] at h_step'
  sorry

end CamelUp.Invariants.RollBatch
