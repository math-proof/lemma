import Lemma.Nat.Add
import Lemma.Nat.Mul
import Lemma.Tensor.AddAppendS.eq.AppendAddS
import Lemma.Tensor.CosAppend.eq.AppendCosS
import Lemma.Tensor.DataMul.eq.MulDataS
import Lemma.Tensor.DataNeg.eq.NegData
import Lemma.Tensor.DotAppendHstack.eq.AppendAddSDotS
import Lemma.Tensor.DotMulEye.eq.Mul
import Lemma.Tensor.RotaryMatrix.eq.AppendHstackSMulSEye
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.MulAppendS.eq.AppendMulS
import Lemma.Tensor.NegStack.eq.Stack_Neg
import Lemma.Tensor.SinAppend.eq.AppendSinS
import Lemma.Vector.GetMul.eq.MulGetS
import Lemma.Vector.GetNeg.eq.NegGet
open Nat Tensor
set_option maxHeartbeats 600000


@[main]
private lemma main
-- given
  (θ : Tensor ℝ [d])
  (x0 x1 : Tensor ℝ [d]) :
-- imply
  (rotaryMatrix θ) @ (x0 ++ x1) = (x0 ++ x1) * (θ ++ θ).cos + (-x1 ++ x0) * (θ ++ θ).sin := by
-- proof
  simp only [rotaryMatrix]
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
  rw [Mul.comm θ.cos x0]
  have hsin : (-θ.sin) * x1 = (-x1) * θ.sin := by
    apply Eq.of.EqDataS
    rw [DataMul.eq.MulDataS, DataMul.eq.MulDataS, DataNeg.eq.NegData, DataNeg.eq.NegData]
    rw [Nat.Mul.comm]
    ext j
    rw [Vector.GetMul.eq.MulGetS.fin, Vector.GetMul.eq.MulGetS.fin,
      Vector.GetNeg.eq.NegGet.fin, Vector.GetNeg.eq.NegGet.fin]
    rw [mul_neg, neg_mul]
  rw [hsin]
  rw [Mul.comm θ.sin x0, Mul.comm θ.cos x1]
  conv_lhs =>
    arg 2
    rw [Add.comm]
  rw [AppendAddS.eq.AddAppendS (A := x0 * θ.cos) (B := x1 * θ.cos) (C := (-x1) * θ.sin) (D := x0 * θ.sin)]
  rw [AppendMulS.eq.MulAppendS x0 θ.cos x1 θ.cos, AppendMulS.eq.MulAppendS (-x1) θ.sin x0 θ.sin]
  rw [CosAppend.eq.AppendCosS θ θ, SinAppend.eq.AppendSinS θ θ]


-- created on 2026-09-03
