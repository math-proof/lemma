import sympy.tensor.tensor
import Lemma.Tensor.ItemNeg.eq.NegItem
open Tensor


@[main]
private lemma main
  [AddGroup α] [LinearOrder α]
-- given
  (a : Tensor α []) :
-- imply
  |a| = if a.item ≤ -a.item then -a else a := by
-- proof
  rw [abs_eq_max_neg, max_def]
  simp only [
    show LE.le (self := (inferInstance : LinearOrder (Tensor α [])).toLE) a (-a) ↔
        a.item ≤ (-a).item from Iff.rfl,
    ItemNeg.eq.NegItem
  ]


-- created on 2026-09-07
