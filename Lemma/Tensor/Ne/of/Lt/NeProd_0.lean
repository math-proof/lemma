import Lemma.Tensor.Lt.is.LtDataS
import Lemma.Vector.Ne.of.Lt.Ne_0
open Tensor Vector


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.Ne.of.Lt.NeProd_0 |
| comm 2 | Tensor.Ne.of.Gt.NeProd_0 |
-/
@[main, comm 2]
private lemma main
  [Preorder α]
  {x y : Tensor α s}
-- given
  (h_s : s.prod ≠ 0)
  (h : x < y) :
-- imply
  x ≠ y := by
-- proof
  intro heq
  subst heq
  rw [Lt.is.LtDataS] at h
  exact Vector.Ne.of.Lt.Ne_0 h_s h rfl


-- created on 2026-08-16
