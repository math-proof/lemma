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
  have hblock :=
    DotAppendS.eq.AppendAddSDotS (I * C) (-(I * S)) (I * S) (I * C) x0 x1
  simp [R]
  rw [hblock]
  have hIc := DotMulEye.eq.Mul θ.cos x0
  have hIs0 := DotMulEye.eq.Mul θ.sin x0
  have hIc1 := DotMulEye.eq.Mul θ.cos x1
  have hstack : -S = [_ < d] (-θ.sin) := by
    apply Tensor.Eq.of.All_EqGetS.fin
    intro i
    have hN := GetNeg.eq.NegGet (S : Tensor α (d :: [d]))
      ⟨(i : ℕ), by simp [Tensor.length]⟩
    have hS := EqGetStack.fin (fun _ : Fin d => θ.sin) i
    have hS' := EqGetStack.fin (fun _ : Fin d => -θ.sin) i
    simp [S, GetElem.getElem] at hN hS hS' ⊢
    rw [hN, hS, hS']
    rfl
  have hnegS : -(I * S) = I * ([_ < d] (-θ.sin)) := by
    apply Eq.of.EqDataS
    rw [DataNeg.eq.NegData, DataMul.eq.MulDataS, DataMul.eq.MulDataS]
    have hd := congrArg Tensor.data hstack
    rw [DataNeg.eq.NegData] at hd
    rw [← hd]
    ext j
    rw [Vector.GetNeg.eq.NegGet.fin, Vector.GetMul.eq.MulGetS.fin, Vector.GetMul.eq.MulGetS.fin]
    rw [Vector.GetNeg.eq.NegGet.fin]
    exact (mul_neg (I.data.get j) (S.data.get j)).symm
  have hIs1 := DotMulEye.eq.Mul (-θ.sin) x1
  rw [hnegS, hIc, hIs0, hIc1, hIs1]
  simp only [id]
  have h0 : θ.cos * x0 + (-θ.sin) * x1 = x0 * θ.cos + (-x1) * θ.sin := by
    rw [mul_comm θ.cos x0]
    congr 1
    apply Eq.of.EqDataS
    rw [DataMul.eq.MulDataS, DataMul.eq.MulDataS, DataNeg.eq.NegData, DataNeg.eq.NegData]
    rw [_root_.mul_comm]
    ext j
    rw [Vector.GetMul.eq.MulGetS.fin, Vector.GetMul.eq.MulGetS.fin,
      Vector.GetNeg.eq.NegGet.fin, Vector.GetNeg.eq.NegGet.fin]
    rw [mul_neg, neg_mul]
  have h1 : θ.sin * x0 + θ.cos * x1 = x1 * θ.cos + x0 * θ.sin := by
    rw [mul_comm θ.sin x0, mul_comm θ.cos x1, _root_.add_comm]
  rw [h0, h1]
  rw [AppendAddS.eq.AddAppendS (A := x0 * θ.cos) (B := x1 * θ.cos) (C := (-x1) * θ.sin) (D := x0 * θ.sin)]
  have hm0 := AppendMulS.eq.MulAppendS x0 θ.cos x1 θ.cos
  have hm1 := AppendMulS.eq.MulAppendS (-x1) θ.sin x0 θ.sin
  rw [hm0, hm1]
  rw [CosAppend.eq.AppendCosS θ θ, SinAppend.eq.AppendSinS θ θ]


-- created on 2023-06-06
-- updated on 2026-08-24
