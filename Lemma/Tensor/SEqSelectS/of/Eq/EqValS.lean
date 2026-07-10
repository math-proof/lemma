import Lemma.Tensor.SEqSelectS.of.SEq.EqValS.EqValS
open Tensor


@[main]
private lemma main
  {X : Tensor α s}
  {d : Fin s.length}
  {d' : Fin s.length}
  {i : Fin s[d]}
  {i' : Fin s[d']}
-- given
  (h_d : d = d')
  (h_i : i.val = i'.val) :
-- imply
  X.select d i ≃ X.select d' i' := by
-- proof
  apply SEqSelectS.of.SEq.EqValS.EqValS _ _ h_i
  ·
    rfl
  ·
    simp_all


-- created on 2026-04-16
