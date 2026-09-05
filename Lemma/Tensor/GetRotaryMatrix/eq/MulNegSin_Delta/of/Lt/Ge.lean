import Lemma.Tensor.GetAppend.eq.Get.of.Lt
import Lemma.Tensor.GetHstack.eq.Get_Sub.of.GtAdd.Ge
import Lemma.Tensor.GetMulEye_Stack.eq.MulDelta
import Lemma.Tensor.GetNeg.eq.NegGet
import Lemma.Tensor.NegMul.eq.MulNeg
import Lemma.Tensor.RotaryMatrix.eq.AppendHstackSMulSEye
open Tensor


@[main]
private lemma main
-- given
  (θ : Tensor ℝ [d])
  (i j : Fin (d + d))
  (hi : i < d)
  (hj : j ≥ d) :
-- imply
  θ.rotaryMatrix[i][j] = -θ.sin[j - d]'(by grind) * (KroneckerDelta (α := Fin d) ⟨i, by grind⟩ ⟨j - d, by grind⟩ : Tensor ℝ []) := by
-- proof
  unfold rotaryMatrix
  extract_lets I
  let C := I * [_ < d] θ.cos
  let S := I * [_ < d] θ.sin
  have hj' : (j : ℕ) - d < d := Nat.sub_lt_left_of_lt_add hj j.isLt
  let i0 : Fin d := ⟨(i : ℕ), hi⟩
  let j0 : Fin d := ⟨(j : ℕ) - d, hj'⟩
  have hrow := GetAppend.eq.Get.of.Lt (n := d) (m := d) hi (C.hstack (-S)) (S.hstack C)
  have hcell := GetHstack.eq.Get_Sub.of.GtAdd.Ge (n := d) (m := d) hj j.isLt C (-S) i0
  have hneg1 := GetNeg.eq.NegGet (X := S) i0
  let Si : Tensor ℝ [d] := S[i0]
  have hneg2 := GetNeg.eq.NegGet (X := Si) j0
  have hm := GetMulEye_Stack.eq.MulDelta θ.sin i0 j0
  simp only [id] at hrow hcell hneg1 hneg2 hm ⊢
  apply (congrArg (fun t : Tensor ℝ [d + d] => t[j]) hrow).trans
  apply hcell.trans
  have hneg : (-S)[i0][j - d] = -id (α := Tensor ℝ []) S[i0][j - d] := by
    have h := congrArg (fun t : Tensor ℝ [d] => t[j - d]) hneg1
    simp only [id, Si] at h hneg2 ⊢
    exact h.trans hneg2
  apply hneg.trans
  apply Eq.trans (congrArg Neg.neg (hm.trans ((Tensor.Mul _ _).trans ((Tensor.Mul.comm _ _).trans (Tensor.Mul _ _).symm))))
  simp [i0, j0]
  apply NegMul.eq.MulNeg.nil


-- created on 2026-09-04
-- updated on 2026-09-05
