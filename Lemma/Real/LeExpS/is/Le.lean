import Lemma.Nat.NotLt.is.Ge
import Lemma.Real.LtExpS.is.Lt
import sympy.functions.elementary.exponential
open Real Nat


@[main, comm, mp, mpr]
private lemma main
  [ExpPos α]
-- given
  (a b : α) :
-- imply
  exp a ≤ exp b ↔ a ≤ b := by
-- proof
  simp [← NotGt.is.Le]
  rw [not_iff_not]
  apply LtExpS.is.Lt


-- created on 2025-12-27
