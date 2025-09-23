import Lemma.Algebra.LtMod.of.Gt_0
import Lemma.Algebra.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Algebra.EqMod.of.Lt
import Lemma.Algebra.Get.eq.GetFlatten_AddMul.of.Lt.Lt
import Lemma.Vector.EqGetReplicate.of.Lt
open Algebra Vector


@[main]
private lemma main
-- given
  (h_n : n > 0)
  (h : k < t * n)
  (v : List.Vector α n) :
-- imply
  have : k % n < n := LtMod.of.Gt_0 h_n k
  (List.Vector.replicate t v).flatten[k] = v[k % n] := by
-- proof
  intro h_k
  obtain ⟨i, h_i, j, h_j, h_ij⟩ := Any_Eq_AddMul.of.Lt_Mul h
  simp [h_ij]
  simp [EqMod.of.Lt h_j]
  rw [GetFlatten_AddMul.eq.Get.of.Lt.Lt (by assumption) (by assumption)]
  rw [EqGetReplicate.of.Lt]


-- created on 2025-07-12
