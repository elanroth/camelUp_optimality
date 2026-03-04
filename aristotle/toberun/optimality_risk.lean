-- Aristotle toberun: risk-sensitive or win-probability objective.
-- This is a placeholder for a non-EV optimality story.

import CamelUp.Model.Types
import CamelUp.Controller.Sim
import CamelUp.Controller.EV
import CamelUp.Controller.Policy

namespace CamelUp.Proofs.OptimalityRisk

open CamelUp CamelUp.Sim CamelUp.EV CamelUp.Policy

/-- Placeholder: a utility function that could prioritize win probability. -/
opaque utility (gs : GameState) : Float

/-- Placeholder: expected utility of a policy. -/
opaque expectedUtility (P : Policy) (gs : GameState) (seed : UInt64) (n : Nat) : Float

/-- A policy that may trade EV for win probability in endgame states. -/
opaque riskAwareBot (n : Nat) : Policy

/-- Sketch: riskAwareBot is optimal for the chosen utility. -/
axiom riskAware_optimal (gs : GameState) (P : Policy) (seed : UInt64)
    (n : Nat) (hn : n > 0) :
    expectedUtility (riskAwareBot n) gs seed n >= expectedUtility P gs seed n

end CamelUp.Proofs.OptimalityRisk
