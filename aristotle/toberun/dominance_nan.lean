-- Aristotle toberun: NaN-freedom chain for EV evaluation.
-- Goal: small lemmas feeding Dominance.lean.

import CamelUp.Model.Types
import CamelUp.Model.Step
import CamelUp.Controller.Sim
import CamelUp.Controller.EV
import CamelUp.Controller.Policy

namespace CamelUp.Dominance.Toberun

open CamelUp CamelUp.Sim CamelUp.EV CamelUp.Policy

/-- `Float` from an `Int` is never NaN. -/
lemma intToFloat_not_nan (i : Int) : ¬(Int.toFloat i).isNaN := by
  sorry

/-- `Float` from a `Nat` is never NaN. -/
lemma natToFloat_not_nan (n : Nat) : ¬(Nat.toFloat n).isNaN := by
  sorry

/-- If `n > 0`, then `n.toFloat` is nonzero. -/
lemma natToFloat_ne_zero (n : Nat) (h : n > 0) : Nat.toFloat n ≠ 0.0 := by
  sorry

/-- `evalState` never produces a NaN mean score. -/
theorem evalState_no_nan (gs : GameState) (player : Nat) (rng : RNG) (n : Nat) :
    ¬(evalState gs player rng n).1.isNaN := by
  sorry

/-- `evalDetMove` never produces a NaN mean score. -/
theorem evalDetMove_no_nan (gs : GameState) (move : Move) (baseline : Float)
    (rng : RNG) (n : Nat) :
    ¬(evalDetMove gs move baseline rng n).1.meanScore.isNaN := by
  sorry

/-- `evalRollAction` never produces a NaN mean score. -/
theorem evalRollAction_no_nan (gs : GameState) (baseline : Float)
    (rng : RNG) (n : Nat) :
    ¬(evalRollAction gs baseline rng n).1.meanScore.isNaN := by
  sorry

/-- Every `MoveEval` in the output of `rankMoves` has a non-NaN mean score. -/
theorem rankMoves_no_nan (gs : GameState) (seed : UInt64) (n : Nat) :
    ∀ me ∈ rankMoves gs seed n, ¬me.meanScore.isNaN := by
  sorry

end CamelUp.Dominance.Toberun
