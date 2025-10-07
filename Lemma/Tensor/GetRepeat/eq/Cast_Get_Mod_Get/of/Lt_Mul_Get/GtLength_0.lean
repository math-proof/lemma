import sympy.tensor.tensor
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Algebra.LtMod.of.Gt_0
import Lemma.Algebra.Gt_0.of.GtMul
import Lemma.List.Set.eq.AppendTake__Cons_Drop.of.Lt_Length
import Lemma.Tensor.GetRepeat.as.Get_Mod_Get.of.Lt_MulGet.GtLength_0
import Lemma.Bool.EqCast.of.SEq
import Lemma.Tensor.LengthRepeat.eq.Mul_Get_0.of.GtLength_0
open Tensor Algebra List Bool


@[main]
private lemma main
-- given
  (h_s : s.length > 0)
  (h_i : i < n * s[0])
  (X : Tensor α s) :
-- imply
  have : i < (X.repeat n ⟨0, h_s⟩).length := by rwa [LengthRepeat.eq.Mul_Get_0.of.GtLength_0]
  have := Gt_0.of.GtMul h_i
  have : i % s[0] < X.length := by
    rw [Length.eq.Get_0.of.GtLength_0 h_s]
    apply LtMod.of.Gt_0
    assumption
  have : s.tail = (s.set 0 (n * s[(⟨0, h_s⟩ : Fin s.length)])).tail := by
    rw [Set.eq.AppendTake__Cons_Drop.of.Lt_Length h_s]
    simp
  (X.repeat n ⟨0, h_s⟩)[i] = cast (by rw [this]) X[i % s[0]] := by
-- proof
  intros
  apply Eq_Cast.of.SEq
  apply GetRepeat.as.Get_Mod_Get.of.Lt_MulGet.GtLength_0 h_s h_i X


@[main]
private lemma fin
-- given
  (h_s : s.length > 0)
  (h_i : i < n * s[0])
  (X : Tensor α s) :
-- imply
  have : i < (X.repeat n ⟨0, h_s⟩).length := by rwa [LengthRepeat.eq.Mul_Get_0.of.GtLength_0]
  have := Gt_0.of.GtMul h_i
  have : i % s[0] < X.length := by
    rw [Length.eq.Get_0.of.GtLength_0 h_s]
    apply LtMod.of.Gt_0
    assumption
  have : s.tail = (s.set 0 (n * s[(⟨0, h_s⟩ : Fin s.length)])).tail := by
    rw [Set.eq.AppendTake__Cons_Drop.of.Lt_Length h_s]
    simp
  (X.repeat n ⟨0, h_s⟩).get ⟨i, by assumption⟩ = cast (by rw [this]) (X.get ⟨i % s[0], by assumption⟩) := by
-- proof
  apply main
  repeat assumption


-- created on 2025-07-11
-- updated on 2025-07-12
