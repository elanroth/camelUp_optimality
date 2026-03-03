/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 95717055-6fc5-41ff-9836-60bf627ee595

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem step_Roll_mods_size (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.Roll outcome) = some gs') :
    gs'.modifiers.size = numSquares

- theorem step_Roll_player_valid (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.Roll outcome) = some gs') :
    gs'.numPlayers > 0 → gs'.currentPlayer < gs'.numPlayers
-/

-- Aristotle Batch: CamelUp.Proofs.Invariants — Roll field lemmas
--
-- These 5 theorems complete the Roll branch of step_preserves_valid.
-- They are currently sorry-stubbed in CamelUp/Proofs/Invariants.lean.
--
-- Key tactic challenge: after `unfold CamelUp.step at h_step`,
-- `split_ifs` behavior inside match arms.  The step function unfolds to:
--
--   if gs.gameOver then none
--   else match move with
--   | .Roll outcome =>
--       if !gs.diceBag.contains outcome.camel then none
--       else
--         let scores₁ := awardPlayer gs.scores gs.currentPlayer 1
--         let newBag   := gs.diceBag.erase outcome.camel
--         let (newBoard, newFinished, mTileOwner) :=
--               applyDie gs.board gs.modifiers gs.finishedCamels outcome
--         let scores₁ := match mTileOwner with
--                        | none   => scores₁
--                        | some p => awardPlayer scores₁ p 1
--         if !newFinished.isEmpty then
--           some { ..., diceBag := [],   gameOver := true }
--         else if newBag.isEmpty then
--           some { ..., diceBag := CamelColor.all, legNo := gs.legNo + 1 }
--         else
--           some { ..., diceBag := newBag }
--
-- The three Roll outcomes (goals after splitting the inner ifs):
--   arm A (race over):  gameOver=true, diceBag=[]
--   arm B (leg end):    gameOver=false, diceBag=CamelColor.all, legNo += 1
--   arm C (mid-leg):    gameOver=false, diceBag=newBag (erase outcome.camel)
--
-- Supporting lemmas already proved in Invariants.lean (can be used freely):
--   bag_each_once_erase : ∀ c bag, (∀ x, bag.count x ≤ 1) →
--       ∀ x, (bag.erase c).count x ≤ 1
--   resolveLegBets_scores_size, resolveRaceWinBets_scores_size,
--   resolveRaceLoseBets_scores_size, awardPlayer_size
--   advancePlayer_lt : ∀ p n, n > 0 → advancePlayer p n < n

import CamelUp.Model.Types
import CamelUp.Model.Step
import CamelUp.Controller.Sim
import CamelUp.Controller.EV
import CamelUp.Controller.Policy
import CamelUp.Proofs.Invariants


namespace CamelUp.Dominance.RollBatch

open CamelUp CamelUp.Sim CamelUp.EV CamelUp.Policy

open CamelUp.Dominance

/- Aristotle took a wrong turn (reason code: 9). Please try again. -/
-- Pull in needed lemmas from Invariants
-- (these are already proved, use them freely)
-- #check bag_each_once_erase
-- #check resolveLegBets_scores_size
-- #check awardPlayer_size
-- #check advancePlayer_lt

/-- Roll: no color appears twice in the remaining dice bag.
    Hint approach A (omega/decide):
      `unfold CamelUp.step at h_step`
      Then try `simp only [...] at h_step` to reduce the if-then-else,
      then `rcases` or `obtain` to case-split on which arm was taken.
    Hint approach B (rcases on h_step directly):
      `rcases (step_cases gs (Move.Roll outcome) gs' h_step) with ...`
      (if such a lemma exists).
    Hint approach C (omega):
      After subst h_step in each arm, the diceBag is concrete:
      - arm A (race over): diceBag=[], count=0 ≤ 1 by simp
      - arm B (leg end):   diceBag=CamelColor.all, count ≤ 1 by `cases c <;> decide`
      - arm C (mid-leg):   use bag_each_once_erase + h_valid.bag_each_once -/
theorem step_Roll_bag_each_once (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.Roll outcome) = some gs') :
    ∀ c : CamelColor, gs'.diceBag.count c ≤ 1 := by
  sorry

/- Aristotle took a wrong turn (reason code: 9). Please try again. -/
/-- Roll: scores array size is preserved.
    Hint: same case-split as bag_each_once.
    - arm A (race over):  scores = resolveRaceLoseBets(resolveRaceWinBets(resolveLegBets(awardPlayer ...)))
      use resolveRaceLoseBets_scores_size, resolveRaceWinBets_scores_size,
          resolveLegBets_scores_size, awardPlayer_size, h_valid.scores_size
    - arm B (leg end):    scores = resolveLegBets(awardPlayer ...)
      use resolveLegBets_scores_size, awardPlayer_size, h_valid.scores_size
    - arm C (mid-leg):    scores = awardPlayer gs.scores gs.currentPlayer 1
      use awardPlayer_size, h_valid.scores_size -/
theorem step_Roll_scores_size (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.Roll outcome) = some gs') :
    gs'.scores.size = gs'.numPlayers := by
  sorry

/- Aristotle took a wrong turn (reason code: 9). Please try again. -/
/-- Roll: legBetTiles array still has 5 entries.
    Hint: CamelColor has 5 constructors, so initialLegBetTiles.size = 5 (decide).
    - arm A: legBetTiles = gs.legBetTiles → exact h_valid.tiles_size
    - arm B: legBetTiles = initialLegBetTiles → decide
    - arm C: legBetTiles = gs.legBetTiles → exact h_valid.tiles_size -/
theorem step_Roll_tiles_size (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.Roll outcome) = some gs') :
    gs'.legBetTiles.size = 5 := by
  sorry

/-- Roll: modifiers array size is preserved (unchanged in all arms).
    Hint: all three arms leave modifiers = gs.modifiers → exact h_valid.mods_size -/
theorem step_Roll_mods_size (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.Roll outcome) = some gs') :
    gs'.modifiers.size = numSquares := by
  convert h_valid.mods_size using 1;
  unfold CamelUp.step at h_step; aesop;

/-- Roll: currentPlayer stays within [0, numPlayers).
    Hint: all three arms set currentPlayer = advancePlayer gs.currentPlayer gs.numPlayers
    → exact advancePlayer_lt gs.currentPlayer gs.numPlayers hn -/
theorem step_Roll_player_valid (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.Roll outcome) = some gs') :
    gs'.numPlayers > 0 → gs'.currentPlayer < gs'.numPlayers := by
  exact?

end CamelUp.Dominance.RollBatch