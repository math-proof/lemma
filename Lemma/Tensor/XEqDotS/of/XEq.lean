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
open Tensor Hyperreal Vector
set_option maxHeartbeats 4000000


private lemma not_infinite_getData
  (X : Tensor ℝ [n])
  (i : Fin n) :
  ¬((X : Tensor ℝ* [n]).data[i] → ∞) := by
  rw [← Any_IsSt.is.NotInfinite]
  refine Exists.intro (X.data[i]) ?_
  simp [Tensor.map, GetElem.getElem]


private def col_real (X : Tensor ℝ [n, m]) (j : Fin m) : Tensor ℝ [n] :=
  (Xᵀ)[j]


private def row_real (X : Tensor ℝ [m, n]) (i : Fin m) : Tensor ℝ [n] :=
  (X[i] : Tensor ℝ [n])


noncomputable def transpose_col (X : Tensor ℝ [n, m]) (j : Fin m) : Tensor ℝ* [n] :=
  Tensor.map Hyperreal.ofReal (col_real X j)


set_option maxHeartbeats 12000000 in
private lemma col_map_transpose_entry
  (X : Tensor ℝ [n, m]) (j : Fin m) (k : Fin n) :
  (Tensor.map Hyperreal.ofReal X)ᵀ[j][k] = Tensor.map Hyperreal.ofReal (X[k][j]) := by
  simp only [GetElem.getElem]
  erw [Tensor.GetTranspose.eq.Get.fin (X := Tensor.map Hyperreal.ofReal X) (i := k) (j := j)]
  erw [GetMap.eq.MapGet.fin (X := X) (f := Hyperreal.ofReal) (i := ⟨k, by simp [Tensor.length]⟩)]
  erw [← Coe.eq.Map (X := X[k])]
  erw [GetMap.eq.MapGet.fin (X := X[k]) (f := Hyperreal.ofReal) (i := ⟨j, by simp [Tensor.length]⟩)]
  simp [Tensor.map, GetElem.getElem]



set_option maxHeartbeats 12000000 in
private lemma col_map_transpose_entry_at
  (X : Tensor ℝ [n, m]) (j : Fin m) (i : Fin n) :
  (Tensor.map Hyperreal.ofReal X)ᵀ[j][i] = (transpose_col X j)[i] := by
  have h₁ := col_map_transpose_entry X j i
  have h₂ : Tensor.map Hyperreal.ofReal (X[i][j]) = (transpose_col X j)[i] := by
    dsimp [transpose_col]
    simp only [GetElem.getElem]
    erw [GetMap.eq.MapGet.fin (X := col_real X j) (f := Hyperreal.ofReal) (i := i)]
    simp only [col_real, GetElem.getElem]
    erw [← Tensor.GetTranspose.eq.Get.fin (X := X) (i := i) (j := j)]
    rfl
  exact h₁.trans h₂


set_option maxHeartbeats 12000000 in
private lemma coerce_transpose_col_entry
  (X : Tensor ℝ [n, m]) (j : Fin m) (i : Fin n) :
  ((X : Tensor ℝ* [n, m])ᵀ)[j][i] = (transpose_col X j)[i] := by
  conv_lhs =>
    erw [← Coe.eq.Map (X := X)]
    simp only [GetElem.getElem]
  exact col_map_transpose_entry_at X j i


set_option maxHeartbeats 12000000 in
private lemma transpose_col_eq
  (X : Tensor ℝ [n, m]) (j : Fin m) :
  transpose_col X j = ((X : Tensor ℝ* [n, m])ᵀ)[j] := by
  apply Eq.of.EqDataS
  have hn : n = [n].prod := by simp
  refine List.Vector.ext ?_
  intro k
  convert (coerce_transpose_col_entry X j (Fin.cast hn.symm k)).symm using 1
  · simp [transpose_col, col_real, GetElem.getElem, hn]
  · simp [GetElem.getElem, hn]
  · conv =>
      erw [← Coe.eq.Map (X := X)]
      simp [GetElem.getElem, hn]


noncomputable def row_hr (X : Tensor ℝ [m, n]) (i : Fin m) : Tensor ℝ* [n] :=
  (row_real X i : Tensor ℝ* [n])


private lemma map_row_get
  (X : Tensor ℝ [m, n]) (i : Fin m) :
  ((X : Tensor ℝ* [m, n])[i]) = row_hr X i := by
  dsimp only [row_hr, row_real]
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
  exact absurd h (NotInfiniteMul.of.NotInfinite.NotInfinite (not_infinite_getData B i) (not_infinite_getData col i))


private lemma not_infinite_transpose_col
  (X : Tensor ℝ [n, m]) (j : Fin m) (i : Fin n) :
  ¬((transpose_col X j).data[i] → ∞) := by
  dsimp [transpose_col]
  exact not_infinite_getData (col_real X j) i


private lemma not_infinite_transpose_col_mul
  (B : Tensor ℝ [n]) (X : Tensor ℝ [n, m]) (j : Fin m) (i : Fin n) :
  ¬(((B : Tensor ℝ* [n]) * transpose_col X j).data[i] → ∞) := by
  dsimp [transpose_col]
  exact mul_entry_not_infinite B (col_real X j) i


private lemma not_infinite_row
  (X : Tensor ℝ [m, n]) (i : Fin m) (k : Fin n) :
  ¬((row_hr X i).data[k] → ∞) := by
  exact not_infinite_getData (row_real X i) k


private lemma not_infinite_row_mul
  (B : Tensor ℝ [n]) (X : Tensor ℝ [m, n]) (i : Fin m) (k : Fin n) :
  ¬(((B : Tensor ℝ* [n]) * row_hr X i).data[k] → ∞) := by
  dsimp [row_hr]
  exact mul_entry_not_infinite B (row_real X i) k


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
  (A @ (X : Tensor ℝ* [n, m])).get ⟨j, hj⟩ = A @ transpose_col X j := by
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
  ((X : Tensor ℝ* [m, n]) @ A).get ⟨i, hi⟩ = (row_hr X i) @ A := by
-- proof
  have h := GetDot.eq.DotGet.une (X : Tensor ℝ* [m, n]) A i
  conv_lhs => simp [GetElem.getElem]
  rw [← map_row_get X i]
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
