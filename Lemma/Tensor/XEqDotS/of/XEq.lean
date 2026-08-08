import Lemma.Tensor.NotInfiniteGetData
import Lemma.Tensor.SEqMapS.of.SEq
import Lemma.Bool.SEq.is.Eq
import Lemma.Hyperreal.Any_IsSt.is.NotInfinite
import Lemma.Hyperreal.Infinitesimal0
import Lemma.Hyperreal.NotInfiniteMul.of.NotInfinite.NotInfinite
import Lemma.Tensor.Coe.eq.Map
import Lemma.Tensor.DataMul.eq.MulDataS
import Lemma.Tensor.Dot
import Lemma.Tensor.GetData.eq.GetDataGet.of.Lt
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


private lemma col_map_transpose_entry
  (X : Tensor ℝ [n, m]) (j : Fin m) (k : Fin n) :
  (Tensor.map Hyperreal.ofReal X)ᵀ[j][k] = Tensor.map Hyperreal.ofReal (X[k][j]) := by
  simp only [GetElem.getElem]
  erw [Tensor.GetTranspose.eq.Get.fin (X := Tensor.map Hyperreal.ofReal X) (i := k) (j := j)]
  erw [GetMap.eq.MapGet.fin (X := X) (f := Hyperreal.ofReal) (i := ⟨k, by simp [Tensor.length]⟩)]
  erw [← Coe.eq.Map (X := X[k])]
  erw [GetMap.eq.MapGet.fin (X := X[k]) (f := Hyperreal.ofReal) (i := ⟨j, by simp [Tensor.length]⟩)]
  simp [Tensor.map, GetElem.getElem]


private lemma col_map_transpose_entry_at
  (X : Tensor ℝ [n, m]) (j : Fin m) (i : Fin n) :
  (Tensor.map Hyperreal.ofReal X)ᵀ[j][i] = (let col : Tensor ℝ [n] := Xᵀ[j]; col : Tensor ℝ* [n])[i] := by
  have h₁ := col_map_transpose_entry X j i
  have h₂ : Tensor.map Hyperreal.ofReal (X[i][j]) = (let col : Tensor ℝ [n] := Xᵀ[j]; col : Tensor ℝ* [n])[i] := by
    simp only [GetElem.getElem]
    erw [GetMap.eq.MapGet.fin (X := Xᵀ[j]) (f := Hyperreal.ofReal) (i := i)]
    simp only [GetElem.getElem]
    simp
    apply Eq.of.SEq
    apply SEqMapS.of.SEq
    apply SEq.of.Eq
    apply Tensor.Get.eq.GetTranspose.fin
  exact h₁.trans h₂


private lemma coerce_transpose_col_entry
  (X : Tensor ℝ [n, m]) (j : Fin m) (i : Fin n) :
  ((X : Tensor ℝ* [n, m])ᵀ)[j][i] = (let col : Tensor ℝ [n] := Xᵀ[j]; col : Tensor ℝ* [n])[i] := by
  conv_lhs =>
    erw [← Coe.eq.Map (X := X)]
    simp only [GetElem.getElem]
  exact col_map_transpose_entry_at X j i


private lemma fin_tensor_data_get (Y : Tensor ℝ* [n]) (k : Fin [n].prod) (hn : n = [n].prod) :
  Y.data[k] = Y[Fin.cast hn.symm k].data[0] := by
  have hi : k.val < n := Nat.lt_of_lt_of_eq k.isLt hn.symm
  exact GetData.eq.GetDataGet.of.Lt hi Y (i := k.val)


private lemma transpose_col_data_entry
  (X : Tensor ℝ [n, m]) (j : Fin m) (k : Fin [n].prod) (hn : n = [n].prod) :
  (let col : Tensor ℝ [n] := Xᵀ[j]; col : Tensor ℝ* [n]).data[k] = ((X : Tensor ℝ* [n, m])ᵀ)[j].data[k] := by
  let hk : Fin n := Fin.cast hn.symm k
  rw [fin_tensor_data_get (let col : Tensor ℝ [n] := Xᵀ[j]; col : Tensor ℝ* [n]) k hn]
  rw [← coerce_transpose_col_entry X j hk]
  exact Eq.symm (fin_tensor_data_get (Tensor.map Hyperreal.ofReal X)ᵀ[j] k hn)


private lemma transpose_col_eq
  (X : Tensor ℝ [n, m]) (j : Fin m) :
  (let col : Tensor ℝ [n] := Xᵀ[j]; col : Tensor ℝ* [n]) = ((X : Tensor ℝ* [n, m])ᵀ)[j] := by
  apply Eq.of.EqDataS
  have hn : n = [n].prod := by simp
  refine List.Vector.ext ?_
  intro k
  exact transpose_col_data_entry X j k hn


private lemma map_row_get
  (X : Tensor ℝ [m, n]) (i : Fin m) :
  ((X : Tensor ℝ* [m, n])[i]) = (let row : Tensor ℝ [n] := X[i]; row : Tensor ℝ* [n]) := by
  apply Eq.of.EqDataS
  apply List.Vector.ext
  intro k
  simp only [GetElem.getElem]
  conv_lhs =>
    erw [← Coe.eq.Map (X := X)]
    erw [GetMap.eq.MapGet.fin (X := X) (f := Hyperreal.ofReal) (i := ⟨i, by simp [Tensor.length]⟩)]
    erw [← Coe.eq.Map (X := X[i])]
  rfl


private lemma mul_entry_not_infinite
  (B col : Tensor ℝ [n]) (i : Fin n) :
  ¬(((B : Tensor ℝ* [n]) * (col : Tensor ℝ* [n])).data[i] → ∞) := by
  intro h
  rw [DataMul.eq.MulDataS (A := (B : Tensor ℝ* [n])) (B := (col : Tensor ℝ* [n]))] at h
  simp only [GetElem.getElem, Vector.GetMul.eq.MulGetS.fin] at h
  exact absurd h (NotInfiniteMul.of.NotInfinite.NotInfinite (NotInfiniteGetData B ⟨i, by grind⟩) (NotInfiniteGetData col ⟨i, by grind⟩))


private lemma not_infinite_transpose_col
  (X : Tensor ℝ [n, m]) (j : Fin m) (i : Fin n) :
  ¬((let col : Tensor ℝ [n] := Xᵀ[j]; col : Tensor ℝ* [n]).data[i] → ∞) :=
  NotInfiniteGetData Xᵀ[j] ⟨i, by simp [List.EqSwap_0'1]⟩


private lemma not_infinite_transpose_col_mul
  (B : Tensor ℝ [n]) (X : Tensor ℝ [n, m]) (j : Fin m) (i : Fin n) :
  ¬(((B : Tensor ℝ* [n]) * (let col : Tensor ℝ [n] := Xᵀ[j]; col : Tensor ℝ* [n])).data[i] → ∞) := by
  exact mul_entry_not_infinite B Xᵀ[j] i


private lemma not_infinite_row
  (X : Tensor ℝ [m, n]) (i : Fin m) (k : Fin n) :
  ¬((let row : Tensor ℝ [n] := X[i]; row : Tensor ℝ* [n]).data[k] → ∞) :=
  NotInfiniteGetData X[i] ⟨k, by grind⟩


private lemma not_infinite_row_mul
  (B : Tensor ℝ [n]) (X : Tensor ℝ [m, n]) (i : Fin m) (k : Fin n) :
  ¬(((B : Tensor ℝ* [n]) * (let row : Tensor ℝ [n] := X[i]; row : Tensor ℝ* [n])).data[k] → ∞) := by
  exact mul_entry_not_infinite B X[i] k


private lemma dot_vec
  {A B c : Tensor ℝ* [n]}
-- given
  (h_xinfty : ∀ i : Fin n, (c.data[i] → ∞) → A.data[i]⁻¹ ≈ B.data[i]⁻¹)
  (h_or :
    (∀ i : Fin n, ¬((B * c).data[i] → ∞)) ∨
    (B * c ≥ 0) ∨
    (B * c ≤ 0))
  (h : A ≈ B) :
-- imply
  A @ c ≈ B @ c := by
-- proof
  rw [Dot.eq.SumMul__0, Dot.eq.SumMul__0]
  have h_mul : A * c ≈ B * c := by
    apply XEq.of.XEqDataS
    rw [DataMul.eq.MulDataS, DataMul.eq.MulDataS]
    refine Vector.XEq.of.All_XEqGetS.fin ?_
    intro i
    have hn : n = [n].prod := by simp
    rw [Vector.GetMul.eq.MulGetS.fin A.data c.data i, Vector.GetMul.eq.MulGetS.fin B.data c.data i]
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
  (A : Tensor ℝ* [n]) (X : Tensor ℝ [n, m]) (j : Fin m)
  (hj : j < (A @ (X : Tensor ℝ* [n, m])).length := by simp [matmul_shape]; grind) :
-- imply
  (A @ (X : Tensor ℝ* [n, m])).get ⟨j, hj⟩ = A @ (let col : Tensor ℝ [n] := Xᵀ.get j; col : Tensor ℝ* [n]) := by
-- proof
  rw [GetDot.eq.Dot_GetT.fin A (X : Tensor ℝ* [n, m]) j]
  conv_lhs => simp [GetElem.getElem]
  congr 1
  exact Eq.symm (transpose_col_eq X j)


private lemma get_row
-- given
  (X : Tensor ℝ [m, n]) (A : Tensor ℝ* [n]) (i : Fin m)
  (hi : i < ((X : Tensor ℝ* [m, n]) @ A).length := by simp [matmul_shape]; grind) :
-- imply
  ((X : Tensor ℝ* [m, n]) @ A).get ⟨i, hi⟩ = (let row : Tensor ℝ [n] := X[i]; row : Tensor ℝ* [n]) @ A := by
-- proof
  have h := GetDot.eq.DotGet.une (X : Tensor ℝ* [m, n]) A i
  conv_lhs => simp [GetElem.getElem]
  erw [← map_row_get X i]
  exact h


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
  exact dot_vec
    (fun i h_inf => absurd h_inf (not_infinite_transpose_col X j i))
    (Or.inl fun i => not_infinite_transpose_col_mul B X j i)
    (by simpa [B'] using h)


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
  exact dot_vec
    (fun k h_inf => absurd h_inf (not_infinite_row X i k))
    (Or.inl fun k => not_infinite_row_mul B X i k)
    (by simpa [B'] using h)


-- created on 2026-07-29
