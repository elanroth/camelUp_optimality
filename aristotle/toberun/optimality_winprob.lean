-- Aristotle toberun: win-probability (WP) formalization sketch.
-- Goal: define a recursive win-probability functional with small lemmas.

import CamelUp.Model.Types
import CamelUp.Model.Step
import CamelUp.Controller.Sim
import CamelUp.Controller.Policy

namespace CamelUp.Proofs.WinProb

open CamelUp CamelUp.Sim CamelUp.Policy

/-- Probability that `player` eventually wins starting from `gs` under policy `P`.
    This is left opaque to avoid termination/measure issues for now. -/
opaque winProb (P : Policy) (gs : GameState) (player : Nat) : Float

/-- One-step unfolding rule for winProb along a legal move.
    (Placeholder: replace with a recursive equation once termination is settled.) -/
axiom winProb_step
  (P : Policy) (gs : GameState) (player : Nat) (move : Move) (gs' : GameState)
  (h_step : step gs move = some gs') :
  winProb P gs player = winProb P gs' player

/-- If the game is already over, the win probability is 1 for the winner, 0 otherwise. -/
axiom winProb_terminal
  (P : Policy) (gs : GameState) (player : Nat) :
  gs.gameOver = true ->
  winProb P gs player =
    if player = (winnerFromState gs) then 1.0 else 0.0

/-- Placeholder: define winnerFromState on terminal positions. -/
opaque winnerFromState (gs : GameState) : Nat

/-- A policy intended to maximize win probability (may be non-EV). -/
opaque wpBot (n : Nat) : Policy

/-- Sketch: wpBot maximizes win probability among policies. -/
axiom wpBot_optimal
  (gs : GameState) (player : Nat) (P : Policy) :
  winProb (wpBot 1) gs player >= winProb P gs player

end CamelUp.Proofs.WinProb
