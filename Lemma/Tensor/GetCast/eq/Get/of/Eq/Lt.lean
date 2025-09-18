import sympy.tensor.Basic
import Lemma.Algebra.GetCast.eq.Get.of.Eq
open Algebra


@[main]
private lemma main
-- given
  (h_i : i < m)
  (h : m = m')
  (v : List.Vector (Tensor α s) m) :
-- imply
  have h : List.Vector (Tensor α s) m = List.Vector (Tensor α s) m' := by rw [h]
  (cast h v)[i] = v[i] := by
-- proof
  let i : Fin m := ⟨i, h_i⟩
  have := GetCast.eq.Get.of.Eq h v i
  simp [i] at this
  assumption


@[main]
private lemma fin
-- given
  (h_i : i < m)
  (h : m = m')
  (v : List.Vector (Tensor α s) m) :
-- imply
  have h : List.Vector (Tensor α s) m = List.Vector (Tensor α s) m' := by rw [h]
  (cast h v).get ⟨i, by simp_all⟩ = v.get ⟨i, h_i⟩ := by
-- proof
  apply main
  assumption


-- created on 2025-07-05
-- updated on 2025-07-09
