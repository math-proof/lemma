import Lemma.Int.Mul_Sub.eq.SubMulS
import Lemma.Nat.CoeSub.eq.SubCoeS.of.Ge
import Lemma.Nat.ValSub.eq.SubValS.of.Ge
import Lemma.Tensor.DataMul.eq.MulData
import Lemma.Tensor.DataSub.eq.SubDataS
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqGetStack
import Lemma.Vector.GetMul.eq.MulGet
import Lemma.Vector.GetSub.eq.SubGetS
open Int Nat Tensor Vector


private lemma eq_get
  {n d : ℕ}
  {θ : Tensor ℝ [n, d]}
  {τ : Tensor ℝ [d]}
-- given
  (hθ : θ = [i < n] (τ * (i : ℝ)))
  (k : Fin n) :
-- imply
  θ[k] = τ * (k : ℝ) := by
-- proof
  rw [hθ]
  exact EqGetStack.fin (fun i : Fin n => τ * (i : ℝ)) k


private lemma mul_sub_right
  (X : Tensor ℝ s)
  (a b : ℝ) :
  X * a - X * b = X * (a - b) := by
  apply Eq.of.EqDataS
  rw [DataSub.eq.SubDataS, DataMul.eq.MulData, DataMul.eq.MulData, DataMul.eq.MulData]
  ext i
  rw [GetSub.eq.SubGetS.fin, GetMul.eq.MulGet.fin, GetMul.eq.MulGet.fin, GetMul.eq.MulGet.fin]
  exact SubMulS.eq.Mul_Sub (X.data.get i) a b


@[main]
private lemma main
  {n d : ℕ}
  {θ : Tensor ℝ [n, d]}
  {τ : Tensor ℝ [d]}
  {k t : Fin n}
-- given
  (hle : k ≥ t)
  (hθ : θ = [i < n] (τ * (i : ℝ))) :
-- imply
  θ[k] - θ[t] = θ[k - t] := by
-- proof
  rw [eq_get hθ k, eq_get hθ t, eq_get hθ (k - t)]
  apply Eq.trans (mul_sub_right τ (k : ℝ) (t : ℝ))
  rw [← CoeSub.eq.SubCoeS.of.Ge hle, ValSub.eq.SubValS.of.Ge hle]


-- created on 2026-09-03
