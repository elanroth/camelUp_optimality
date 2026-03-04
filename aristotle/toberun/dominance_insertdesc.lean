-- Aristotle toberun: insertDesc head-is-maximum lemma (NaN-free).

import CamelUp.Model.Types
import CamelUp.Controller.EV

namespace CamelUp.Dominance.Toberun

open CamelUp CamelUp.EV

/-- Non-NaN implies `x >= x` for Float. -/
lemma float_ge_self_of_not_nan (x : Float) (h : ¬x.isNaN) : x >= x := by
  sorry

/-- Head of a descending list dominates all members (NaN-free). -/
lemma head_ge_of_desc (lst : List MoveEval)
    (h_no_nan : ∀ me ∈ lst, ¬me.meanScore.isNaN)
    (h_sorted : ∀ me ∈ lst, lst.head?.map (·.meanScore) ≥ some me.meanScore) :
    ∀ me ∈ lst, lst.head?.map (·.meanScore) ≥ some me.meanScore := by
  sorry

/-- The insertion-sort used in `rankMoves` (descending by `meanScore`). -/
private def insertDesc (lst : List MoveEval) (x : MoveEval) : List MoveEval :=
  match lst with
  | []     => [x]
  | h :: t => if x.meanScore >= h.meanScore then x :: h :: t
              else h :: insertDesc t x

/-- After inserting `x`, the head of the result is >= every element (NaN-free). -/
theorem insertDesc_head_ge (lst : List MoveEval) (x : MoveEval)
    (h_no_nan_x   : ¬x.meanScore.isNaN)
    (h_no_nan_lst : ∀ me ∈ lst, ¬me.meanScore.isNaN)
    (h_sorted : ∀ me ∈ lst, lst.head?.map (·.meanScore) ≥ some me.meanScore) :
    ∀ me ∈ insertDesc lst x,
      (insertDesc lst x).head?.map (·.meanScore) ≥ some me.meanScore := by
  sorry

end CamelUp.Dominance.Toberun
