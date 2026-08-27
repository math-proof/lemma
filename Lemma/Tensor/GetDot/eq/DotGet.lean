import Lemma.Bool.Cast.of.SEq.Eq
import Lemma.Bool.SEq.is.Eq
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.Ne_Nil.is.GeLength_1
import Lemma.Tensor.Dot.eq.GetSumMul
import Lemma.Tensor.Dot.eq.SelectSumMul
import Lemma.Tensor.Dot.eq.SumMul
import Lemma.Tensor.Dot.eq.SumMulResizeS_0
import Lemma.Tensor.EqGetUnsqueeze_0
import Lemma.Tensor.Get.of.Eq.GtLength_0
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import Lemma.Tensor.SEqGetS.of.SEq.GtLength
import Lemma.Tensor.SEqMulS.of.SEq.SEq
import Lemma.Tensor.GetMul.eq.MulGetS
import Lemma.Tensor.GetRepeat.as.RepeatGet.of.GtGet_0.GtVal_0
import Lemma.Tensor.GetRepeat_0.as.Get_Mod_Get.of.GtMul_Get.GtLength_0
import Lemma.Tensor.GetResize.as.ResizeGet.of.GtGet_0.GtVal_0
import Lemma.Tensor.GetSelect_1.as.Get.of.Lt.GtGet_0.GtLength_0
import Lemma.Tensor.GetSum.as.SumGet.of.GtGet_0.Gt_0.GtLength
import Lemma.Tensor.GetSum_2.eq.SumGet__1
import Lemma.Tensor.GetUnsqueeze.as.UnsqueezeGet.of.GtGet_0.Gt_0.GtLength_0
import Lemma.Tensor.GtLengthDot.of.LeLengthS.Ne_Nil
import Lemma.Tensor.LengthGet.eq.Get_0.of.GtGet_0.GtLength_1
import Lemma.Tensor.SEqRepeatS.of.SEq
import Lemma.Tensor.SEqSumS.of.SEq
import Lemma.Tensor.SEqUnsqueezeS.of.SEq
open Bool List Tensor
set_option maxHeartbeats 1000000


@[main, fin]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (X : Tensor α [n, k])
  (Y : Tensor α [n', k'])
  (i : Fin n) :
-- imply
  (X @ Y)[i]'(GtLengthDot.of.LeLengthS.Ne_Nil (by simp) (by apply GeLength_1.of.Ne_Nil (by simp)) X Y i) = X[i] @ Y := by
-- proof
  simp [GetElem.getElem]
  rw [Dot.eq.SumMul.resize]
  erw [GetSum_2.eq.SumGet__1.fin (i := ⟨i, by grind⟩)]
  erw [Dot.eq.GetSumMul.resize]
  erw [GetSum_2.eq.SumGet__1.fin (i := ⟨0, by grind⟩)]
  apply Eq.of.SEq
  apply SEqSumS.of.SEq
  repeat rw [@Tensor.GetMul.eq.MulGetS.fin]
  apply SEqMulS.of.SEq.SEq
  <;> erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (s' := [1, k', k ⊔ n']) (i := ⟨0, by grind⟩) (by grind) (by grind)]
  <;> conv_lhs => erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (s' := [n, k', k ⊔ n']) (i := ⟨i, by grind⟩) (by grind) (by grind)];
  <;> apply SEqCastS.of.SEq.Eq.Eq (by simp) (by simp)
  ·
    erw [GetRepeat.eq.Cast_RepeatGet.of.GtGet_0.GtVal_0.fin (by grind) (by grind)]
    conv_rhs => erw [GetRepeat.eq.Cast_RepeatGet.of.GtGet_0.GtVal_0.fin (by grind) (by grind)]
    apply SEqCastS.of.SEq.Eq.Eq (by simp) (by simp)
    apply SEqRepeatS.of.SEq
    erw [GetUnsqueeze.eq.Cast_UnsqueezeGet.of.GtGet_0.Gt_0.GtLength_0.fin (by grind) (by grind) (by grind)]
    conv_rhs => erw [GetUnsqueeze.eq.Cast_UnsqueezeGet.of.GtGet_0.Gt_0.GtLength_0.fin (by grind) (by grind) (by grind)]
    apply SEqCastS.of.SEq.Eq.Eq (by simp) (by simp)
    apply SEqUnsqueezeS.of.SEq
    erw [EqGetUnsqueeze_0.fin]
    apply GetResize.as.ResizeGet.of.GtGet_0.GtVal_0 (by grind) (by grind)
  ·
    erw [GetRepeat_0.eq.Cast_Get_Mod_Get.of.GtMul_Get.GtLength_0.fin (by grind) (by grind)]
    conv_rhs => erw [GetRepeat_0.eq.Cast_Get_Mod_Get.of.GtMul_Get.GtLength_0.fin (by grind) (by grind)]
    apply SEqCastS.of.SEq.Eq.Eq (by simp) (by simp)
    erw [Tensor.EqGetUnsqueeze_0.fin]
    erw [Tensor.EqGetUnsqueeze_0.nat.fin]
    rfl


@[main, fin]
private lemma une
  [Mul α] [Add α] [Zero α]
-- given
  (X : Tensor α [n, k])
  (Y : Tensor α [n'])
  (i : Fin n) :
-- imply
  (X @ Y)[i]'(GtLengthDot.of.LeLengthS.Ne_Nil (by simp) (by simp) X Y i) = X[i] @ Y := by
-- proof
  simp [GetElem.getElem]
  have h := Dot.eq.SelectSumMul.resize X Y
  dsimp at h
  have hget := Get.of.Eq.GtLength_0
    (s := matmul_shape [n, k] [n'])
    (by simp [matmul_shape])
    h
    ⟨i, by simp [matmul_shape]⟩
  simp at hget
  rw [hget]
  apply Eq.of.SEq
  let P := (X.resize 1 (k ⊔ n')).unsqueeze 1 * cast (congrArg (Tensor α) (by simp)) ((((Y.resize 0 (k ⊔ n')).unsqueeze 0).unsqueeze 0).repeat ⟨0, by simp⟩ n)
  let S := P.sum 2
  have hsel := GetSelect_1.as.Get.of.Lt.GtGet_0.GtLength_0
    (i := 0) (j := i.val)
    (s := ((([n, k].set 1 (k ⊔ n')).insertIdx 1 1).eraseIdx 2).tail)
    (by simp) (by simp) i.isLt S
  apply hsel.trans
  have hdot := Dot.eq.SumMulResizeS_0 (X.get ⟨i, i.isLt⟩) Y
  dsimp at hdot
  refine SEq.trans ?_ (SEq.of.Eq hdot.symm)
  have hsum1 := GetSum.as.SumGet.of.GtGet_0.Gt_0.GtLength.fin
    (d := 2) (i := i.val)
    (s := (([n, k].set 1 (k ⊔ n')).insertIdx 1 1))
    (by simp) (by simp) i.isLt P
  have hlen1 := LengthGet.eq.Get_0.of.GtGet_0.GtLength_1
    (s := ((([n, k].set 1 (k ⊔ n')).insertIdx 1 1).eraseIdx 2))
    (by simp) i.isLt (P.sum 2)
  simp [List.set, List.insertIdx, List.eraseIdx] at hlen1
  apply (SEqGetS.of.SEq.GtLength (Nat.lt_of_lt_of_eq Nat.zero_lt_one hlen1.symm) hsum1).trans
  have hsum0 := GetSum.as.SumGet.of.GtGet_0.Gt_0.GtLength.fin
    (d := 1) (i := 0)
    (by simp) (by simp) (by simp)
    (P.get ⟨i, i.isLt⟩)
  apply hsum0.trans
  apply SEqSumS.of.SEq
  simp
  erw [GetMul.eq.MulGetS.fin]
  erw [GetMul.eq.MulGetS.fin]
  apply SEqMulS.of.SEq.SEq
  ·
    have hlenU := LengthGet.eq.Get_0.of.GtGet_0.GtLength_1
      (s := (([n, k].set 1 (k ⊔ n')).insertIdx 1 1))
      (by simp) i.isLt ((X.resize 1 (k ⊔ n')).unsqueeze 1)
    simp [List.set, List.insertIdx] at hlenU
    apply (SEqGetS.of.SEq.GtLength (Nat.lt_of_lt_of_eq Nat.zero_lt_one hlenU.symm)
      (GetUnsqueeze.as.UnsqueezeGet.of.GtGet_0.Gt_0.GtLength_0
        (s := ([n, k].set 1 (k ⊔ n')))
        (by simp) (by simp) i.isLt
        (X.resize 1 (k ⊔ n')))).trans
    simp
    have hu0 := EqGetUnsqueeze_0.fin ((X.resize ⟨1, by simp⟩ (k ⊔ n')).get ⟨i, by simp; exact i.isLt⟩)
    simp [GetElem.getElem] at hu0 ⊢
    rw [hu0]
    have hr := GetResize.as.ResizeGet.of.GtGet_0.GtVal_0
      (s := [n, k]) (d := ⟨1, by simp⟩) (i := i.val)
      (by simp) i.isLt X (k ⊔ n')
    simpa [GetElem.getElem] using hr
  ·
    have hc := GetCast.as.Get.of.Eq.GtLength_0.fin
      (s' := (([n, k].set 1 (k ⊔ n')).insertIdx 1 1))
      (by simp) (by simp)
      ((((Y.resize 0 (k ⊔ n')).unsqueeze 0).unsqueeze 0).repeat ⟨0, by simp⟩ n)
      ⟨i, by simp⟩
    have hlenC := LengthGet.eq.Get_0.of.GtGet_0.GtLength_1
      (s := (([n, k].set 1 (k ⊔ n')).insertIdx 1 1))
      (by simp) i.isLt
      (cast (congrArg (Tensor α) (by simp)) ((((Y.resize 0 (k ⊔ n')).unsqueeze 0).unsqueeze 0).repeat ⟨0, by simp⟩ n))
    simp [List.set, List.insertIdx] at hlenC
    apply (SEqGetS.of.SEq.GtLength (Nat.lt_of_lt_of_eq Nat.zero_lt_one hlenC.symm) hc).trans
    let Yuu := ((Y.resize 0 (k ⊔ n')).unsqueeze 0).unsqueeze 0
    have hr0 := GetRepeat_0.as.Get_Mod_Get.of.GtMul_Get.GtLength_0.fin
      (s := [1, 1, k ⊔ n']) (n := n) (i := i.val)
      (by simp) (by simp) Yuu
    simp [Nat.mod_one] at hr0
    have hlenR := LengthGet.eq.Get_0.of.GtGet_0.GtLength_1
      (s := [1, 1, k ⊔ n'].set 0 (n * [1, 1, k ⊔ n'][0]))
      (by simp) (by simp; exact i.isLt) (Yuu.repeat ⟨0, by simp⟩ n)
    simp [List.set] at hlenR
    apply (SEqGetS.of.SEq.GtLength (Nat.lt_of_lt_of_eq Nat.zero_lt_one hlenR.symm) hr0).trans
    simp [Yuu]
    have hu1 := EqGetUnsqueeze_0.fin ((Y.resize 0 (k ⊔ n')).unsqueeze 0)
    have hlenU1 := LengthGet.eq.Get_0.of.GtGet_0.GtLength_1
      (s := (([n'].set 0 (k ⊔ n')).insertIdx 0 1).insertIdx 0 1)
      (i := 0)
      (by simp) (by simp)
      (((Y.resize 0 (k ⊔ n')).unsqueeze 0).unsqueeze 0)
    simp [List.set, List.insertIdx] at hlenU1
    apply (SEqGetS.of.SEq.GtLength (Nat.lt_of_lt_of_eq Nat.zero_lt_one hlenU1.symm) (SEq.of.Eq hu1)).trans
    apply SEq.of.Eq
    apply EqGetUnsqueeze_0.fin


-- created on 2026-01-05
-- updated on 2026-08-27
