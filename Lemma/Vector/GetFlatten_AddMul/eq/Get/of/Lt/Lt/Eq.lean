import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Vector.GetFlatten_AddMul.eq.Get.of.Lt.Lt
open Nat Vector


@[main, fin]
private lemma main
-- given
  (h_n : n' = n)
  (h_i : i < m)
  (h_j : j < n)
  (v : List.Vector (List.Vector α n) m) :
-- imply
  v.flatten[i * n' + j]'(by simp_all [AddMul.lt.Mul.of.Lt.Lt h_i h_j]) = v[i, j] := by
-- proof
  subst h_n
  apply GetFlatten_AddMul.eq.Get.of.Lt.Lt h_i h_j


-- created on 2026-04-24
