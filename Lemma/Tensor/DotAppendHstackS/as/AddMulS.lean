import Lemma.Bool.SEq.is.Eq
import Lemma.Tensor.AddAppendS.eq.AppendAddS
import Lemma.Tensor.MulAppendS.eq.AppendMulS
import Lemma.Tensor.CosAppend.eq.AppendCosS
import Lemma.Tensor.DataMul.eq.MulDataS
import Lemma.Tensor.DataNeg.eq.NegData
import Lemma.Tensor.DotAppendHstack.eq.AppendAddSDotS
import Lemma.Tensor.DotMulEye.eq.Mul
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.NegStack.eq.Stack_Neg
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
  ((Tensor.eye d * [_ < d] θ.cos).hstack (-(Tensor.eye d * [_ < d] θ.sin)) ++
      (Tensor.eye d * [_ < d] θ.sin).hstack (Tensor.eye d * [_ < d] θ.cos)) @ (x0 ++ x1) ≃
    (x0 ++ x1) * (θ ++ θ).cos + ((-x1) ++ x0) * (θ ++ θ).sin := by
-- proof
  apply SEq.of.Eq
  rw [DotAppendHstack.eq.AppendAddSDotS (Tensor.eye d * [_ < d] θ.cos) (-(Tensor.eye d * [_ < d] θ.sin)) (Tensor.eye d * [_ < d] θ.sin) (Tensor.eye d * [_ < d] θ.cos) x0 x1]
  have hnegS : -(Tensor.eye d * [_ < d] θ.sin) = Tensor.eye d * ([_ < d] (-θ.sin)) := by
    apply Eq.of.EqDataS
    rw [DataNeg.eq.NegData, DataMul.eq.MulDataS, DataMul.eq.MulDataS]
    rw [← congrArg Tensor.data (NegStack.eq.Stack_Neg (fun _ : Fin d => θ.sin))]
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
-- updated on 2026-09-02
