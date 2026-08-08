import Lemma.Tensor.NotInfiniteGetDataMul
import Lemma.Tensor.TMap.eq.MapT
import Lemma.Vector.Head.of.SEq
import Lemma.Tensor.GetData.eq.HeadDataGet.of.Lt
import Lemma.Tensor.NotInfiniteGetData
import Lemma.Tensor.SEqMapS.of.SEq
import Lemma.Bool.SEq.is.Eq
import Lemma.Hyperreal.Any_IsSt.is.NotInfinite
import Lemma.Hyperreal.Infinitesimal0
import Lemma.Hyperreal.NotInfiniteMul.of.NotInfinite.NotInfinite
import Lemma.Tensor.Coe.eq.Map
import Lemma.Tensor.DataMul.eq.MulDataS
import Lemma.Tensor.Dot
import Lemma.Tensor.GetDot.eq.DotGet
import Lemma.Tensor.GetDot.eq.Dot_GetT
import Lemma.Tensor.GetMap.eq.MapGet
import Lemma.Tensor.GetTranspose.eq.Get
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.XEq.is.All_XEqGetS.of.GtLength_0
import Lemma.Tensor.XEq.is.XEqDataS
import Lemma.Tensor.XEqSumS.of.XEq.OrAll_NotInfinite
import Lemma.Vector.GetMul.eq.MulGetS
import Lemma.Vector.XEq.is.All_XEqGetS
import Lemma.Hyperreal.XEqMulS.of.XEq.Imp_XEqInvS
open Tensor Hyperreal Vector Bool
set_option maxHeartbeats 1000000


private lemma dot_vec
  {A B X : Tensor ℝ* [n]}
-- given
  (h_xinfty : ∀ i : Fin n, (X.data[i] → ∞) → A.data[i]⁻¹ ≈ B.data[i]⁻¹)
  (h_or : (∀ i : Fin n, ¬((B * X).data[i] → ∞)) ∨ (B * X ≥ 0) ∨ (B * X ≤ 0))
  (h : A ≈ B) :
-- imply
  A @ X ≈ B @ X := by
-- proof
  rw [Dot.eq.SumMul__0, Dot.eq.SumMul__0]
  have h_mul : A * X ≈ B * X := by
    apply XEq.of.XEqDataS
    rw [DataMul.eq.MulDataS, DataMul.eq.MulDataS]
    refine Vector.XEq.of.All_XEqGetS.fin ?_
    intro i
    have hn : n = [n].prod := by simp
    rw [Vector.GetMul.eq.MulGetS.fin A.data X.data i, Vector.GetMul.eq.MulGetS.fin B.data X.data i]
    exact XEqMulS.of.XEq.Imp_XEqInvS
      (All_XEqGetS.of.XEq.fin (XEqDataS.of.XEq h) i)
      (h_xinfty (Fin.cast hn.symm i))
  obtain h_fin | h_ge | h_le := h_or
  have hn : n = [n].prod := by simp
  ·
    exact XEqSumS.of.XEq.OrAll_NotInfinite
      (Or.inl fun i => h_fin (Fin.cast hn.symm i)) h_mul 0
  ·
    exact XEqSumS.of.XEq.OrAll_NotInfinite (Or.inr (Or.inl h_ge)) h_mul 0
  ·
    exact XEqSumS.of.XEq.OrAll_NotInfinite (Or.inr (Or.inr h_le)) h_mul 0


private lemma get_dot
-- given
  (A : Tensor ℝ* [n]) (X : Tensor ℝ [n, m]) (j : Fin m) :
-- imply
  (A @ (X : Tensor ℝ* [n, m])).get ⟨j, by simp [matmul_shape]; grind⟩ = A @ (let col : Tensor ℝ [n] := Xᵀ.get j; col : Tensor ℝ* [n]) := by
-- proof
  rw [GetDot.eq.Dot_GetT.fin A (X : Tensor ℝ* [n, m]) j]
  conv_lhs => simp [GetElem.getElem]
  congr 1
  symm
  apply Eq.of.EqDataS
  ext i
  rw [GetData.eq.GetDataGet.of.Lt.fin (by grind) (i := i)]
  simp
  conv_lhs => erw [MapGet.eq.GetMap.fin]
  symm
  apply (GetData.eq.HeadDataGet.of.Lt.fin (by grind) ((X : Tensor ℝ* [n, m])ᵀ.get j) (i := i)).trans
  rw [TMap.eq.MapT]
  rfl


private lemma get_row
-- given
  (X : Tensor ℝ [m, n]) (A : Tensor ℝ* [n]) (i : Fin m)
  (hi : i < ((X : Tensor ℝ* [m, n]) @ A).length := by simp [matmul_shape]; grind) :
-- imply
  ((X : Tensor ℝ* [m, n]) @ A).get ⟨i, hi⟩ = (let row : Tensor ℝ [n] := X[i]; row : Tensor ℝ* [n]) @ A := by
-- proof
  have h := GetDot.eq.DotGet.une.fin (X : Tensor ℝ* [m, n]) A i
  simp at h
  conv_lhs => simp [GetElem.getElem]
  apply h.trans
  congr 1
  apply Eq.of.EqDataS
  apply List.Vector.ext
  intro j
  conv_lhs =>
    erw [Map.eq.Coe (X := X)]
    erw [GetMap.eq.MapGet.fin (X := X) (f := Hyperreal.ofReal) (i := ⟨i, by simp [Tensor.length]⟩)]
    erw [Map.eq.Coe (X := X[i])]
  rfl


@[main]
private lemma main
  {A : Tensor ℝ* [n]}
  {B : Tensor ℝ [n]}
  {X : Tensor ℝ [n, m]}
-- given
  (h : A ≈ (B : Tensor ℝ* [n])) :
-- imply
  A @ (X : Tensor ℝ* [n, m]) ≈ (B : Tensor ℝ* [n]) @ (X : Tensor ℝ* [n, m]) := by
-- proof
  let B' : Tensor ℝ* [n] := B
  apply XEq.of.All_XEqGetS.GtLength_0 (h := by simp [matmul_shape])
  intro j
  rw [get_dot A X j, get_dot B' X j]
  refine dot_vec (fun i h_inf => absurd h_inf ?_) (Or.inl fun i => ?_) (by simpa [B'] using h)
  .
    apply NotInfiniteGetData Xᵀ[j] ⟨i, by simp [List.EqSwap_0'1]⟩
  .
    apply NotInfiniteGetDataMul B Xᵀ[j] ⟨i, by grind⟩


@[main]
private lemma left
  {A : Tensor ℝ* [n]}
  {B : Tensor ℝ [n]}
  {X : Tensor ℝ [m, n]}
-- given
  (h : A ≈ (B : Tensor ℝ* [n])) :
-- imply
  (X : Tensor ℝ* [m, n]) @ A ≈ (X : Tensor ℝ* [m, n]) @ (B : Tensor ℝ* [n]) := by
-- proof
  let B' : Tensor ℝ* [n] := B
  apply XEq.of.All_XEqGetS.GtLength_0 (h := by simp [matmul_shape])
  intro i
  rw [get_row X A i, get_row X B' i]
  rw [Dot.comm]
  conv_rhs => rw [Dot.comm]
  refine dot_vec (fun j h_inf => absurd h_inf ?_) (Or.inl fun j => ?_) (by simpa [B'] using h)
  .
    apply NotInfiniteGetData X[i] ⟨j, by grind⟩
  .
    apply NotInfiniteGetDataMul B X[i] ⟨j, by grind⟩


-- created on 2026-07-29
