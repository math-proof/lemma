import stdlib.List.Vector
import Lemma.Algebra.EqMin_SubMulS
open Algebra


@[main]
private lemma main
-- given
  (v : List.Vector α (m * n))
  (i : Fin m) :
-- imply
  v.unflatten[i].val = (v.array_slice (i * n) n).val := by
-- proof
  simp [List.Vector.unflatten]
  simp [List.Vector.range]
  simp [GetElem.getElem]
  simp [List.Vector.get]
  congr
  ·
    rw [EqMin_SubMulS]
  ·
    simp
    congr
    simp_all


-- created on 2025-05-10
