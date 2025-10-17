import Lemma.Tensor.GetRepeat.as.RepeatGet.of.Lt_Get_0.GtVal_0
import Lemma.Tensor.LengthRepeat.eq.Get_0.of.GtVal_0
import Lemma.Tensor.SEq.of.All_SEqGetS.Eq.Ne_Nil
import Lemma.Tensor.LengthRepeat.eq.Mul_Get_0.of.GtLength_0
import Lemma.Tensor.GetRepeat.as.Get_Mod_Get.of.Lt_MulGet.GtLength_0
import Lemma.Tensor.GetCast.eq.Cast_Get.of.Eq.GtLength_0
import Lemma.List.Set.ne.Nil.of.Ne_Nil
import Lemma.List.Ne_Nil.of.GtLength
import Lemma.Bool.SEqCast.of.Eq.Eq
import Lemma.Bool.SEq.of.SEq.SEq
import Lemma.Nat.LtVal
import Lemma.Nat.Gt_0.of.GtMul
import Lemma.Nat.LtMod.of.Gt_0
import Lemma.Nat.Gt_0.of.Gt
import Lemma.Tensor.Length.eq.Get_0.of.GtLength
open Tensor List Bool Nat


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h : s = s')
  (h_d : d < s.length)
  (X : Tensor α s)
  (n : ℕ) :
-- imply
  X.permuteTail n ≃ (cast (congrArg (Tensor α) h) X).permuteTail n := by
-- proof
  induction d generalizing s s' X with
  | zero =>
    apply SEq.of.All_SEqGetS.Eq.Ne_Nil
    ·
      sorry
    ·
      intro i
      have h_i := LtVal i
      sorry
    .
      sorry
  | succ d ih =>
    apply SEq.of.All_SEqGetS.Eq.Ne_Nil
    ·
      sorry
    ·
      intro i
      have h_i := LtVal i
      have h_s := Gt_0.of.Gt h_d
      have h_pos : (⟨d + 1, by assumption⟩ : Fin s.length).val > 0 := by simp
      sorry
    .
      sorry


-- created on 2025-10-17
