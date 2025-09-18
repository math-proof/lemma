import Lemma.Algebra.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Algebra.Get.eq.GetFlatten_AddMul
open Algebra


@[main, comm]
private lemma main
-- given
  (h_i : i < m)
  (h_j : j < n)
  (v : List.Vector (List.Vector α n) m) :
-- imply
  have := AddMul.lt.Mul.of.Lt.Lt h_i h_j
  v[i, j] = v.flatten[i * n + j] :=
-- proof
  Get.eq.GetFlatten_AddMul v ⟨i, h_i⟩ ⟨j, h_j⟩


@[main, comm]
private lemma fin
-- given
  (h_i : i < m)
  (h_j : j < n)
  (v : List.Vector (List.Vector α n) m) :
-- imply
  have h_ij := AddMul.lt.Mul.of.Lt.Lt h_i h_j
  (v.get ⟨i, h_i⟩).get ⟨j, h_j⟩ = v.flatten.get ⟨i * n + j, h_ij⟩ := by
-- proof
  apply main


-- created on 2025-07-09
