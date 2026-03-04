-- Aristotle toberun: Roll branch field lemmas for ValidState.

import CamelUp.Model.Types
import CamelUp.Model.Step
import CamelUp.Controller.Sim
import CamelUp.Controller.EV
import CamelUp.Controller.Policy
import CamelUp.Proofs.Invariants

namespace CamelUp.Invariants.Toberun

open CamelUp CamelUp.Sim CamelUp.EV CamelUp.Policy

/-- Roll: no color appears twice in the remaining dice bag. -/
theorem step_Roll_bag_each_once (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : CamelUp.step gs (Move.Roll outcome) = some gs') :
    ∀ c : CamelColor, gs'.diceBag.count c ≤ 1 := by
  sorry

/-- Roll: scores array size is preserved. -/
theorem step_Roll_scores_size (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : CamelUp.step gs (Move.Roll outcome) = some gs') :
    gs'.scores.size = gs'.numPlayers := by
  sorry

/-- Roll: legBetTiles array still has 5 entries. -/
theorem step_Roll_tiles_size (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : CamelUp.step gs (Move.Roll outcome) = some gs') :
    gs'.legBetTiles.size = 5 := by
  sorry

/-- Roll: currentPlayer stays within [0, numPlayers). -/
theorem step_Roll_player_valid (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : CamelUp.step gs (Move.Roll outcome) = some gs') :
    gs'.numPlayers > 0 → gs'.currentPlayer < gs'.numPlayers := by
  sorry

end CamelUp.Invariants.Toberun
