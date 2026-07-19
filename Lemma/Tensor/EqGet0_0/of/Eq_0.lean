import Lemma.Tensor.GtLength
import Lemma.Tensor.EqGet0_0
open Tensor


@[main, fin]
private lemma main
  [Zero α]
  {X : Tensor α s}
-- given
  (h : X = 0)
  (i : Fin X.length) :
-- imply
  X[i] = 0 :=
-- proof
  h.symm.subst (motive := fun X : Tensor α s => X[i]'(by apply GtLength) = 0) (EqGet0_0 ⟨i, by grind⟩)


-- created on 2025-12-06
