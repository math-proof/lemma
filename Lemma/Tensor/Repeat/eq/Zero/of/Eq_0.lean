import Lemma.Tensor.EqRepeat_0'0
import Lemma.Vector.EqRepeat_0'0
import sympy.tensor.tensor
open Tensor Vector


@[main]
private lemma main
  [Zero α]
-- given
  (h : n = 0)
  (X : Tensor α s)
  (d : Fin s.length) :
-- imply
  X.repeat d n = 0 :=
-- proof
  h.symm.subst (motive := fun n => X.repeat d n = 0) (EqRepeat_0'0 X d)


-- created on 2026-07-12
