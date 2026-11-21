import Notation.Algebra.Power
import Instance.Data.Tensor.Tensor.Part2
import Lemma.Tensor.ItemMul.eq.MulItemS
open Tensor


@[path]
private lemma main
  [Monoid α]
-- given
  (a : Tensor α []) :
-- imply
  a².item = a.item² := by
-- proof
  rw [pow_two, pow_two]
  change (Mul.mul a a).item = a.item * a.item
  exact ItemMul.eq.MulItemS a a


-- created on 2026-09-07
-- updated on 2026-11-20
