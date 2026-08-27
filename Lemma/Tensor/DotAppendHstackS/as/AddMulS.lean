import Lemma.Bool.SEq.is.Eq
import Lemma.Tensor.AddAppendS.eq.AppendAddS
import Lemma.Tensor.MulAppendS.eq.AppendMulS
import Lemma.Tensor.CosAppend.eq.AppendCosS
import Lemma.Tensor.DataMul.eq.MulDataS
import Lemma.Tensor.DataNeg.eq.NegData
import Lemma.Tensor.DotAppendS.eq.AppendAddSDotS
import Lemma.Tensor.DotMulEye.eq.Mul
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.GetNeg.eq.NegGet
import Lemma.Tensor.SinAppend.eq.AppendSinS
import Lemma.Vector.GetMul.eq.MulGetS
import Lemma.Vector.GetNeg.eq.NegGet
import sympy.tensor.functions
open Bool Tensor
set_option maxHeartbeats 600000


/--
1D rotary embedding (RoPE) on a split token vector.

`R(θ) @ (x₀ ++ x₁) ≃ (x₀ ++ x₁) * cos(θ ++ θ) + ((-x₁) ++ x₀) * sin(θ ++ θ)`.
-/
@[main]
private lemma rotary
  [CommRing α] [CharZero α] [Cos α] [Sin α]
-- given
  (θ x0 x1 : Tensor α [d]) :
-- imply
  let I : Tensor α [d, d] := Tensor.eye d
  let C : Tensor α [d, d] := [_ < d] θ.cos
  let S : Tensor α [d, d] := [_ < d] θ.sin
  let R := Tensor.hstack (I * C) (-(I * S)) ++ Tensor.hstack (I * S) (I * C)
  R @ (x0 ++ x1) ≃
    (x0 ++ x1) * (θ ++ θ).cos + ((-x1) ++ x0) * (θ ++ θ).sin := by
-- proof
  intro I C S R
  apply SEq.of.Eq
  simp [R]
  rw [DotAppendS.eq.AppendAddSDotS (I * C) (-(I * S)) (I * S) (I * C) x0 x1]
  have hnegS : -(I * S) = I * ([_ < d] (-θ.sin)) := by
    apply Eq.of.EqDataS
    rw [DataNeg.eq.NegData, DataMul.eq.MulDataS, DataMul.eq.MulDataS]
    rw [← congrArg Tensor.data (?hstack : -S = [_ < d] (-θ.sin))]
    case hstack =>
      apply Tensor.Eq.of.All_EqGetS.fin
      intro i
      have hN := GetNeg.eq.NegGet (S : Tensor α (d :: [d])) ⟨(i : ℕ), by simp [Tensor.length]⟩
      have hS := EqGetStack.fin (fun _ : Fin d => θ.sin) i
      have hS' := EqGetStack.fin (fun _ : Fin d => -θ.sin) i
      simp [S, GetElem.getElem] at hN hS hS' ⊢
      erw [hN, hS, hS']
      rfl
    rw [DataNeg.eq.NegData]
    ext j
    rw [Vector.GetNeg.eq.NegGet.fin, Vector.GetMul.eq.MulGetS.fin, Vector.GetMul.eq.MulGetS.fin]
    rw [Vector.GetNeg.eq.NegGet.fin]
    apply Eq.symm
    apply mul_neg
  rw [
    hnegS,
    DotMulEye.eq.Mul θ.cos x0,
    DotMulEye.eq.Mul θ.sin x0,
    DotMulEye.eq.Mul θ.cos x1,
    DotMulEye.eq.Mul (-θ.sin) x1
  ]
  simp only [id]
  rw [mul_comm θ.cos x0]
  have hsin : (-θ.sin) * x1 = (-x1) * θ.sin := by
    apply Eq.of.EqDataS
    rw [DataMul.eq.MulDataS, DataMul.eq.MulDataS, DataNeg.eq.NegData, DataNeg.eq.NegData]
    rw [_root_.mul_comm]
    ext j
    rw [Vector.GetMul.eq.MulGetS.fin, Vector.GetMul.eq.MulGetS.fin,
      Vector.GetNeg.eq.NegGet.fin, Vector.GetNeg.eq.NegGet.fin]
    rw [mul_neg, neg_mul]
  rw [hsin]
  rw [mul_comm θ.sin x0, mul_comm θ.cos x1]
  conv_lhs =>
    arg 2
    rw [_root_.add_comm]
  rw [AppendAddS.eq.AddAppendS (A := x0 * θ.cos) (B := x1 * θ.cos) (C := (-x1) * θ.sin) (D := x0 * θ.sin)]
  rw [AppendMulS.eq.MulAppendS x0 θ.cos x1 θ.cos, AppendMulS.eq.MulAppendS (-x1) θ.sin x0 θ.sin]
  rw [CosAppend.eq.AppendCosS θ θ, SinAppend.eq.AppendSinS θ θ]


-- created on 2023-06-06
-- updated on 2026-08-27
