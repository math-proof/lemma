module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic

public section

open Real
open scoped Matrix


namespace FusionRing

variable {ι : Type*} [Fintype ι]

private lemma sum_pos_mul_nonneg_eq_zero_imp
    {a : ι → ℝ} {u : ι → ℝ}
    (ha : ∀ i, 0 < a i)
    (hu : ∀ i, 0 ≤ u i)
    (hsum : ∑ i, a i * u i = 0) :
    ∀ i, u i = 0 := by
  intro i
  have h_nonneg : ∀ j, 0 ≤ a j * u j := fun j => mul_nonneg (le_of_lt (ha j)) (hu j)
  have h_le := Finset.single_le_sum (f := fun j => a j * u j)
    (fun j _ => h_nonneg j) (Finset.mem_univ i)
  have h_eq : a i * u i = 0 := le_antisymm (by linarith) (h_nonneg i)
  exact (mul_eq_zero.mp h_eq).resolve_left (ne_of_gt (ha i))

private lemma mulVec_diff_eq
    (M : Matrix ι ι ℝ) (r s : ℝ) (v w : ι → ℝ) (c : ℝ)
    (hev : M.mulVec v = r • v)
    (hew : M.mulVec w = s • w)
    (k : ι) :
    (∑ i, M k i * (w i - c * v i)) = s * w k - c * r * v k := by
  have h1 : ∑ i, M k i * w i = s * w k := by
    have := congr_fun hew k
    simp [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this; linarith
  have h2 : ∑ i, M k i * v i = r * v k := by
    have := congr_fun hev k
    simp [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this; linarith
  simp_rw [mul_sub]; rw [Finset.sum_sub_distrib]
  have h3 : ∑ x, M k x * (c * v x) = c * r * v k := by
    simp_rw [← mul_assoc, mul_comm (M k _) c, mul_assoc]; rw [← Finset.mul_sum, h2]
  linarith

namespace PerronFrobeniusGeneral

/-- Uniqueness of positive eigenvectors for a strictly positive matrix. -/
public theorem pfUnique_general
    [Nonempty ι]
    (M : Matrix ι ι ℝ)
    (hM : ∀ i j, 0 < M i j)
    (r₁ r₂ : ℝ) (v w : ι → ℝ)
    (hv : ∀ i, 0 < v i) (hev : M.mulVec v = r₁ • v)
    (hw : ∀ i, 0 < w i) (hew : M.mulVec w = r₂ • w) :
    ∃ c : ℝ, ∀ i, w i = c * v i := by
  obtain ⟨j, _, hj_min⟩ := Finset.exists_min_image Finset.univ (fun i => w i / v i)
    Finset.univ_nonempty
  set c := w j / v j
  have hc_pos : 0 < c := div_pos (hw j) (hv j)
  have hv_ne : ∀ i, v i ≠ 0 := fun i => ne_of_gt (hv i)
  have hw_ne : ∀ i, w i ≠ 0 := fun i => ne_of_gt (hw i)
  have hge : ∀ i, c * v i ≤ w i := by
    intro i
    have hi : c ≤ w i / v i := hj_min i (Finset.mem_univ i)
    rwa [le_div_iff₀ (hv i)] at hi
  have hu_nonneg : ∀ i, 0 ≤ w i - c * v i := fun i => by linarith [hge i]
  have hu_j : w j - c * v j = 0 := by
    show w j - w j / v j * v j = 0; rw [div_mul_cancel₀ (w j) (hv_ne j)]; ring
  have hw_j_eq : w j = c * v j := by linarith
  have hMu_j' : ∑ i, M j i * (w i - c * v i) = (r₂ - r₁) * c * v j := by
    rw [mulVec_diff_eq M r₁ r₂ v w c hev hew j, hw_j_eq]; ring
  have hMu_nonneg : 0 ≤ ∑ i, M j i * (w i - c * v i) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (le_of_lt (hM j i)) (hu_nonneg i)
  have hr₂_ge : r₁ ≤ r₂ := by
    by_contra h; push Not at h
    have : (r₂ - r₁) * c * v j < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) hc_pos) (hv j)
    linarith
  obtain ⟨k, _, hk_min⟩ := Finset.exists_min_image Finset.univ (fun i => v i / w i)
    Finset.univ_nonempty
  set d := v k / w k
  have hd_pos : 0 < d := div_pos (hv k) (hw k)
  have hge' : ∀ i, d * w i ≤ v i := by
    intro i
    have hi : d ≤ v i / w i := hk_min i (Finset.mem_univ i)
    rwa [le_div_iff₀ (hw i)] at hi
  have hu'_nonneg : ∀ i, 0 ≤ v i - d * w i := fun i => by linarith [hge' i]
  have hv_k_eq : v k = d * w k := by
    have : v k - d * w k = 0 := by
      show v k - v k / w k * w k = 0; rw [div_mul_cancel₀ (v k) (hw_ne k)]; ring
    linarith
  have hMu'_k' : ∑ i, M k i * (v i - d * w i) = (r₁ - r₂) * d * w k := by
    rw [mulVec_diff_eq M r₂ r₁ w v d hew hev k, hv_k_eq]; ring
  have hMu'_nonneg : 0 ≤ ∑ i, M k i * (v i - d * w i) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (le_of_lt (hM k i)) (hu'_nonneg i)
  have hr₁_ge : r₂ ≤ r₁ := by
    by_contra h; push Not at h
    have : (r₁ - r₂) * d * w k < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) hd_pos) (hw k)
    linarith
  have hr_eq : r₁ = r₂ := le_antisymm hr₂_ge hr₁_ge
  have hMu_zero : ∑ i, M j i * (w i - c * v i) = 0 := by rw [hMu_j']; simp [hr_eq]
  have hu_zero : ∀ i, w i - c * v i = 0 :=
    sum_pos_mul_nonneg_eq_zero_imp (a := (M j ·)) (u := fun i => w i - c * v i) (hM j) hu_nonneg hMu_zero
  exact ⟨c, fun i => by linarith [hu_zero i]⟩

end PerronFrobeniusGeneral

/-- Uniqueness part of EGNO Theorem 1.44.1: any two positive
eigenvectors of a strictly positive matrix are scalar multiples
of each other. -/
public theorem theorem_1_44_1_uniqueness
    {ι : Type*} [DecidableEq ι] [Fintype ι] [Nonempty ι]
    (M : Matrix ι ι ℝ) (hM : ∀ i j, 0 < M i j)
    (r₁ r₂ : ℝ) (v w : ι → ℝ)
    (hv : ∀ i, 0 < v i) (hev : M.mulVec v = r₁ • v)
    (hw : ∀ i, 0 < w i) (hew : M.mulVec w = r₂ • w) :
    ∃ c : ℝ, ∀ i, w i = c * v i :=
  PerronFrobeniusGeneral.pfUnique_general M hM r₁ r₂ v w hv hev hw hew

end FusionRing
