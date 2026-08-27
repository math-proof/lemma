import Lemma.Tensor.NotInfiniteGetDataMul
import Lemma.Tensor.TMap.eq.MapT
import Lemma.Tensor.GetData.eq.HeadDataGet.of.Lt
import Lemma.Tensor.GetDot.eq.Dot_GetT
import Lemma.Tensor.XEq.is.All_XEqGetS.of.GtLength_0
import Lemma.Tensor.XEqDotS.of.XEq.OrAll_NotInfinite.All_Imp_XEqInvS
import Lemma.Vector.Head.eq.Get_0
open Tensor Vector


private lemma get_col
-- given
  (A : Tensor ℝ* [n]) (X : Tensor ℝ [n, m])
  (j : Fin m) :
-- imply
  (A @ (X : Tensor ℝ* [n, m])).get ⟨j, by simp [matmul_shape]; grind⟩ = A @ (id (α := Tensor ℝ [n]) (Xᵀ.get j) : Tensor ℝ* [n]) := by
-- proof
  rw [GetDot.eq.Dot_GetT.fin A (X : Tensor ℝ* [n, m]) j]
  conv_lhs => simp [GetElem.getElem]
  congr 1
  symm
  apply Eq.of.EqDataS
  ext i
  rw [GetData.eq.GetDataGet.of.Lt.fin (by grind) (i := i)]
  conv_lhs => erw [MapGet.eq.GetMap.fin]
  symm
  apply (GetData.eq.HeadDataGet.of.Lt.fin (by grind) ((X : Tensor ℝ* [n, m])ᵀ.get j) (i := i)).trans
  rw [TMap.eq.MapT]
  erw [Head.eq.Get_0.fin]
  rfl


private lemma get_row
-- given
  (X : Tensor ℝ [m, n])
  (A : Tensor ℝ* [n])
  (i : Fin m) :
-- imply
  ((X : Tensor ℝ* [m, n]) @ A).get ⟨i, by grind [matmul_shape]⟩ = (id (α := Tensor ℝ [n]) X[i] : Tensor ℝ* [n]) @ A := by
-- proof
  have h := GetDot.eq.DotGet.une.fin (X : Tensor ℝ* [m, n]) A i
  simp at h
  conv_lhs => simp [GetElem.getElem]
  apply h.trans
  congr 1
  apply Eq.of.EqDataS
  apply List.Vector.ext
  intro j
  conv_lhs => erw [GetMap.eq.MapGet.fin]
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
  rw [get_col A X j, get_col B' X j]
  refine XEqDotS.of.XEq.OrAll_NotInfinite.All_Imp_XEqInvS (fun i h_inf => absurd h_inf ?_) (Or.inl fun i => ?_) (by simpa [B'] using h)
  .
    apply NotInfiniteGetData Xᵀ[j] ⟨i, by simp⟩
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
  rw [@Tensor.Dot.comm]
  conv_rhs => rw [@Tensor.Dot.comm]
  refine XEqDotS.of.XEq.OrAll_NotInfinite.All_Imp_XEqInvS (fun j h_inf => absurd h_inf ?_) (Or.inl fun j => ?_) (by simpa [B'] using h)
  .
    apply NotInfiniteGetData X[i] ⟨j, by grind⟩
  .
    apply NotInfiniteGetDataMul B X[i] ⟨j, by grind⟩


-- created on 2026-07-29
-- updated on 2026-08-19
