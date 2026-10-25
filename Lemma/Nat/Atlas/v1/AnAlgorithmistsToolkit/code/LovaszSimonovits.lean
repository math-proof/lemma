import Mathlib
import sympy.Basic
import Def.v1.Atlas.AnAlgorithmistsToolkit.code.LovaszSimonovits
open LovaszSimonovits
open Finset


namespace LovaszSimonovits

/--
[lsCurve_nonincreasing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LovaszSimonovits.lean)
-/
@[path]
lemma lsCurve_nonincreasing
  {n : ℕ}
  {ρ_prev ρ_curr : Fin n → ℝ}
  {x : ℝ}
-- given
  (hstep : RandomWalkStepReal ρ_prev ρ_curr)
  (hclaim8 : WeightedSumInequality ρ_prev)
  (hx0 : 0 ≤ x)
  (hxn : x ≤ ↑n) :
-- imply
  lsCurve ρ_curr x ≤ lsCurve ρ_prev x := by
-- proof
  obtain ⟨c, hc_nonneg, hc_le1, hc_sum, hc_eq⟩ := hstep x hx0 hxn
  rw [hc_eq]
  have h := hclaim8 c hc_nonneg hc_le1
  rwa [hc_sum] at h
open Finset

end LovaszSimonovits

namespace LovaszSimonovits

/--
[all_one_of_sum_ge_n](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LovaszSimonovits.lean)
-/
@[path]
lemma all_one_of_sum_ge_n
  {n : ℕ}
  {c : Fin n → ℝ}
-- given
  (hc1 : ∀ i, c i ≤ 1)
  (hge : (n : ℝ) ≤ univ.sum c) :
-- imply
  ∀ i, c i = 1 := by
-- proof
  have hle : univ.sum c ≤ n := by
    calc univ.sum c ≤ univ.sum (fun _ : Fin n => (1 : ℝ)) :=
      Finset.sum_le_sum (fun i _ => hc1 i)
      _ = n := by simp
  have heq : univ.sum c = n := le_antisymm hle hge
  intro i; by_contra h
  have hlt : c i < 1 := lt_of_le_of_ne (hc1 i) h
  have : univ.sum c < univ.sum (fun _ : Fin n => (1 : ℝ)) :=
    Finset.sum_lt_sum (fun j _ => hc1 j) ⟨i, Finset.mem_univ _, hlt⟩
  simp at this; linarith
set_option maxRecDepth 1000 in

end LovaszSimonovits

namespace LovaszSimonovits

/--
[antitone_weighted_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LovaszSimonovits.lean)
-/
@[path]
lemma antitone_weighted_sum_le
  {n : ℕ}
  {w : Fin n → ℝ}
  {c : Fin n → ℝ}
  {k : Fin n}
  {frac : ℝ}
-- given
  (hw : Antitone w)
  (hc0 : ∀ i, 0 ≤ c i)
  (hc1 : ∀ i, c i ≤ 1)
  (hsum : univ.sum c = k.val + frac) :
-- imply
  univ.sum (fun i => c i * w i) ≤ partialSum w k.val + frac * w k := by
-- proof
  suffices h : univ.sum (fun i => c i * (w i - w k)) ≤
    univ.sum (fun i : Fin n => if i.val < k.val then (w i - w k) else 0) by
    have lhs_eq : univ.sum (fun i => c i * (w i - w k)) =
      univ.sum (fun i => c i * w i) - (↑k.val + frac) * w k := by
      have : univ.sum (fun i => c i * (w i - w k)) =
        univ.sum (fun i => c i * w i) - univ.sum c * w k := by
        simp only [mul_sub]; rw [Finset.sum_sub_distrib]; congr 1; rw [← Finset.sum_mul]
      rw [this, hsum]
    have rhs_eq : univ.sum (fun i : Fin n => if i.val < k.val then (w i - w k) else 0) =
      partialSum w k.val - ↑k.val * w k := by
      simp only [partialSum]
      have : ∀ i : Fin n, (if i.val < k.val then (w i - w k) else (0 : ℝ)) =
        (if i.val < k.val then w i else 0) - (if i.val < k.val then w k else 0) := by
        intro i; split_ifs <;> ring
      simp_rw [this, Finset.sum_sub_distrib]
      congr 1
      trans ((Finset.Iio k).sum (fun _ => w k))
      · rw [← Finset.sum_filter]; congr 1
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_Iio, Fin.lt_def]
      · rw [Finset.sum_const, nsmul_eq_mul, Fin.card_Iio]
    linarith
  apply Finset.sum_le_sum
  intro i _
  split_ifs with hlt
  · have hle : i ≤ k := Fin.le_of_lt (Fin.lt_def.mpr hlt)
    have hwpos : 0 ≤ w i - w k := sub_nonneg.mpr (hw hle)
    linarith [hc1 i, mul_le_mul_of_nonneg_right (hc1 i) hwpos]
  · have hle : k ≤ i := Fin.le_def.mpr (by omega)
    exact mul_nonpos_of_nonneg_of_nonpos (hc0 i) (sub_nonpos.mpr (hw hle))
set_option maxRecDepth 1000 in

end LovaszSimonovits

namespace LovaszSimonovits

/--
[claim8_weighted_sum_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LovaszSimonovits.lean)
-/
@[path]
lemma claim8_weighted_sum_inequality
  {n : ℕ}
  {ρ : Fin n → ℝ}
-- given
  (hconc : LSCurveIsConcave ρ) :
-- imply
  WeightedSumInequality ρ := by
-- proof
  intro c hc0 hc1
  set w := sortedValues ρ; set S := univ.sum c
  have hw : Antitone w := hconc
  by_cases hn : n = 0
  · subst hn; simp [lsCurve]
  simp only [lsCurve, hn, ↓reduceIte]
  have hS_nonneg : 0 ≤ S := Finset.sum_nonneg (fun i _ => hc0 i)
  by_cases hk : Nat.floor S ≥ n
  · simp only [ge_iff_le, hk, ↓reduceDIte]
    have hSn : (n : ℝ) ≤ S := le_trans (Nat.cast_le.mpr hk) (Nat.floor_le hS_nonneg)
    have hallone : ∀ i, c i = 1 := all_one_of_sum_ge_n c hc1 hSn
    have hlhs : univ.sum (fun i => c i * w i) = univ.sum w := by
      congr 1; ext i; rw [hallone i, one_mul]
    have hrhs : partialSum w n = univ.sum w := by
      simp only [partialSum]; congr 1; ext i; simp [show i.val < n from i.isLt]
    linarith
  · simp only [ge_iff_le, hk, ↓reduceDIte]
    have hkn : Nat.floor S < n := by omega
    have hsum_eq : univ.sum c = (⟨Nat.floor S, hkn⟩ : Fin n).val + (S - ↑(Nat.floor S)) := by
      simp; ring
    exact antitone_weighted_sum_le w c hw hc0 hc1 ⟨Nat.floor S, hkn⟩
      (S - ↑(Nat.floor S)) hsum_eq

end LovaszSimonovits

namespace LovaszSimonovits

/--
[theorem10_distribution_evolution](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LovaszSimonovits.lean)
-/
@[path]
lemma theorem10_distribution_evolution
  {n : ℕ}
  {ρ_prev ρ_curr : Fin n → ℝ}
  {φ : ℝ}
-- given
  (hφ : 0 ≤ φ)
  (hφ1 : φ ≤ 1/2)
  (hclaim8 : WeightedSumInequality ρ_prev)
  (hmono : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ ↑n → lsCurve ρ_prev a ≤ lsCurve ρ_prev b)
  (harc_lower : ∀ x : ℝ, 0 ≤ x → x ≤ ↑n / 2 → ∃ c₁ c₂ : Fin n → ℝ, (∀ i, 0 ≤ c₁ i) ∧ (∀ i, c₁ i ≤ 1) ∧ (∀ i, 0 ≤ c₂ i) ∧ (∀ i, c₂ i ≤ 1) ∧ (univ.sum c₁ ≤ x - 2 * φ * x) ∧ (univ.sum c₂ ≤ x + 2 * φ * x) ∧ lsCurve ρ_curr x = (1/2) * univ.sum (fun i => c₁ i * sortedValues ρ_prev i) + (1/2) * univ.sum (fun i => c₂ i * sortedValues ρ_prev i))
  (harc_upper : ∀ x : ℝ, ↑n / 2 ≤ x → x ≤ ↑n → ∃ c₁ c₂ : Fin n → ℝ, (∀ i, 0 ≤ c₁ i) ∧ (∀ i, c₁ i ≤ 1) ∧ (∀ i, 0 ≤ c₂ i) ∧ (∀ i, c₂ i ≤ 1) ∧ (univ.sum c₁ ≤ x - 2 * φ * (↑n - x)) ∧ (univ.sum c₂ ≤ x + 2 * φ * (↑n - x)) ∧ lsCurve ρ_curr x = (1/2) * univ.sum (fun i => c₁ i * sortedValues ρ_prev i) + (1/2) * univ.sum (fun i => c₂ i * sortedValues ρ_prev i)) :
-- imply
  (∀ x : ℝ, 0 ≤ x → x ≤ ↑n / 2 → lsCurve ρ_curr x ≤ (1/2) * (lsCurve ρ_prev (x - 2 * φ * x) + lsCurve ρ_prev (x + 2 * φ * x))) ∧ (∀ x : ℝ, ↑n / 2 ≤ x → x ≤ ↑n → lsCurve ρ_curr x ≤ (1/2) * (lsCurve ρ_prev (x - 2 * φ * (↑n - x)) + lsCurve ρ_prev (x + 2 * φ * (↑n - x)))) := by
-- proof
  constructor
  ·
    intro x hx0 hxm
    obtain ⟨c₁, c₂, hc1_nn, hc1_le, hc2_nn, hc2_le, hsum1, hsum2, heq⟩ :=
      harc_lower x hx0 hxm
    rw [heq]
    have hS1 : (1/2) * univ.sum (fun i => c₁ i * sortedValues ρ_prev i) ≤
      (1/2) * lsCurve ρ_prev (x - 2 * φ * x) := by
      have happ := hclaim8 c₁ hc1_nn hc1_le
      have hsum_nn : 0 ≤ univ.sum c₁ := Finset.sum_nonneg (fun i _ => hc1_nn i)
      have htarget_le_n : x - 2 * φ * x ≤ ↑n := by nlinarith
      have hmono_app := hmono (univ.sum c₁) (x - 2 * φ * x) hsum_nn hsum1 htarget_le_n
      linarith [le_trans happ hmono_app]
    have hS2 : (1/2) * univ.sum (fun i => c₂ i * sortedValues ρ_prev i) ≤
      (1/2) * lsCurve ρ_prev (x + 2 * φ * x) := by
      have happ := hclaim8 c₂ hc2_nn hc2_le
      have hsum_nn : 0 ≤ univ.sum c₂ := Finset.sum_nonneg (fun i _ => hc2_nn i)
      have htarget_le_n : x + 2 * φ * x ≤ ↑n := by nlinarith
      have hmono_app := hmono (univ.sum c₂) (x + 2 * φ * x) hsum_nn hsum2 htarget_le_n
      linarith [le_trans happ hmono_app]
    linarith
  ·
    intro x hxm hxn
    obtain ⟨c₁, c₂, hc1_nn, hc1_le, hc2_nn, hc2_le, hsum1, hsum2, heq⟩ :=
      harc_upper x hxm hxn
    rw [heq]
    have hS1 : (1/2) * univ.sum (fun i => c₁ i * sortedValues ρ_prev i) ≤
      (1/2) * lsCurve ρ_prev (x - 2 * φ * (↑n - x)) := by
      have happ := hclaim8 c₁ hc1_nn hc1_le
      have hsum_nn : 0 ≤ univ.sum c₁ := Finset.sum_nonneg (fun i _ => hc1_nn i)
      have htarget_le_n : x - 2 * φ * (↑n - x) ≤ ↑n := by nlinarith
      have hmono_app := hmono (univ.sum c₁) (x - 2 * φ * (↑n - x)) hsum_nn hsum1 htarget_le_n
      linarith [le_trans happ hmono_app]
    have hS2 : (1/2) * univ.sum (fun i => c₂ i * sortedValues ρ_prev i) ≤
      (1/2) * lsCurve ρ_prev (x + 2 * φ * (↑n - x)) := by
      have happ := hclaim8 c₂ hc2_nn hc2_le
      have hsum_nn : 0 ≤ univ.sum c₂ := Finset.sum_nonneg (fun i _ => hc2_nn i)
      have htarget_le_n : x + 2 * φ * (↑n - x) ≤ ↑n := by nlinarith
      have hmono_app := hmono (univ.sum c₂) (x + 2 * φ * (↑n - x)) hsum_nn hsum2 htarget_le_n
      linarith [le_trans happ hmono_app]
    linarith

end LovaszSimonovits

namespace LovaszSimonovits

/--
[midpoint_mono_pointwise](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LovaszSimonovits.lean)
-/
@[path]
lemma midpoint_mono_pointwise
  {f g : ℝ → ℝ}
  {a b : ℝ}
-- given
  (hfa : f a ≤ g a)
  (hfb : f b ≤ g b) :
-- imply
  (1/2) * (f a + f b) ≤ (1/2) * (g a + g b) := by
-- proof
linarith

end LovaszSimonovits

namespace LovaszSimonovits

/--
[sqrt_one_sub_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LovaszSimonovits.lean)
-/
@[path]
lemma sqrt_one_sub_le
  {t : ℝ}
-- given
  (ht1 : t ≤ 1) :
-- imply
  Real.sqrt (1 - t) ≤ 1 - t / 2 := by
-- proof
  have h1 : (0 : ℝ) ≤ 1 - t / 2 := by linarith
  rw [← Real.sqrt_sq h1]
  apply Real.sqrt_le_sqrt
  linarith [sq_nonneg t]

end LovaszSimonovits

namespace LovaszSimonovits

/--
[sqrt_midpoint_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LovaszSimonovits.lean)
-/
@[path]
lemma sqrt_midpoint_bound
  {φ : ℝ}
-- given
  (hφ : 0 ≤ φ)
  (hφ1 : φ ≤ 1/2) :
-- imply
  (1/2) * (Real.sqrt (1 - 2 * φ) + Real.sqrt (1 + 2 * φ)) ≤ 1 - φ^2 / 2 := by
-- proof
  suffices h : Real.sqrt (1 - 2 * φ) + Real.sqrt (1 + 2 * φ) ≤ 2 - φ^2 by linarith
  have hlhs_nn : 0 ≤ Real.sqrt (1 - 2 * φ) + Real.sqrt (1 + 2 * φ) := by positivity
  have hrhs_nn : (0 : ℝ) ≤ 2 - φ^2 := by nlinarith [sq_nonneg φ]
  have hsq_le : (Real.sqrt (1 - 2 * φ) + Real.sqrt (1 + 2 * φ))^2 ≤ (2 - φ^2)^2 := by
    have lhs_sq : (Real.sqrt (1 - 2 * φ) + Real.sqrt (1 + 2 * φ))^2 =
      2 + 2 * Real.sqrt ((1 - 2 * φ) * (1 + 2 * φ)) := by
      have h1 : Real.sqrt (1 - 2 * φ) ^ 2 = 1 - 2 * φ :=
        Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 1 - 2 * φ)
      have h2 : Real.sqrt (1 + 2 * φ) ^ 2 = 1 + 2 * φ :=
        Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 1 + 2 * φ)
      have h3 : Real.sqrt (1 - 2 * φ) * Real.sqrt (1 + 2 * φ) =
        Real.sqrt ((1 - 2 * φ) * (1 + 2 * φ)) :=
        (Real.sqrt_mul (by linarith : (0 : ℝ) ≤ 1 - 2 * φ) _).symm
      ring_nf; ring_nf at h1 h2 h3; nlinarith [h1, h2, h3]
    rw [lhs_sq, show (2 - φ^2)^2 = 4 - 4 * φ^2 + φ^4 from by ring,
      show (1 - 2 * φ) * (1 + 2 * φ) = 1 - 4 * φ^2 from by ring]
    have hsqrt : Real.sqrt (1 - 4 * φ^2) ≤ 1 - 2 * φ^2 := by
      have := sqrt_one_sub_le (4 * φ^2) (by nlinarith)
      simp only [show 4 * φ ^ 2 / 2 = 2 * φ ^ 2 from by ring] at this
      exact this
    nlinarith [sq_nonneg (φ^2)]
  nlinarith [sq_nonneg (Real.sqrt (1 - 2 * φ) + Real.sqrt (1 + 2 * φ) - (2 - φ^2))]

end LovaszSimonovits

namespace LovaszSimonovits

/--
[midpoint_bound_lower_proof](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LovaszSimonovits.lean)
-/
@[path]
lemma midpoint_bound_lower_proof
  {n : ℕ}
  {φ : ℝ}
-- given
  (hφ : 0 ≤ φ)
  (hφ1 : φ ≤ 1/2)
  (hn : 0 < n) :
-- imply
  MidpointBoundLower n φ := by
-- proof
  intro t x hx0 hxm
  simp only [lovaszSimonovitsBound]
  have hx_le_nx : x ≤ ↑n - x := by linarith
  have hmin_x : min (Real.sqrt x) (Real.sqrt (↑n - x)) = Real.sqrt x :=
    min_eq_left (Real.sqrt_le_sqrt hx_le_nx)
  have hx_sub_le : x * (1 - 2 * φ) ≤ ↑n - x * (1 - 2 * φ) := by nlinarith
  have hrw_sub : x - 2 * φ * x = x * (1 - 2 * φ) := by ring
  have hrw_add : x + 2 * φ * x = x * (1 + 2 * φ) := by ring
  simp only [hrw_sub, hrw_add]
  have hmin_sub : min (Real.sqrt (x * (1 - 2 * φ))) (Real.sqrt (↑n - x * (1 - 2 * φ))) =
    Real.sqrt (x * (1 - 2 * φ)) :=
    min_eq_left (Real.sqrt_le_sqrt hx_sub_le)
  rw [hmin_sub]
  have hmin_add_le : min (Real.sqrt (x * (1 + 2 * φ))) (Real.sqrt (↑n - x * (1 + 2 * φ))) ≤
    Real.sqrt (x * (1 + 2 * φ)) := min_le_left _ _
  have hsqrt_sub : Real.sqrt (x * (1 - 2 * φ)) = Real.sqrt x * Real.sqrt (1 - 2 * φ) :=
    Real.sqrt_mul hx0 _
  have hsqrt_add : Real.sqrt (x * (1 + 2 * φ)) = Real.sqrt x * Real.sqrt (1 + 2 * φ) :=
    Real.sqrt_mul hx0 _
  have hc_nn : (0 : ℝ) ≤ (1 - φ^2 / 2)^t := pow_nonneg (by nlinarith [sq_nonneg φ]) _
  have hct : (1 - φ ^ 2 / 2) ^ (t + 1) = (1 - φ ^ 2 / 2) ^ t * (1 - φ ^ 2 / 2) := pow_succ _ _
  rw [hct, hmin_x]
  have hlinear : (1/2) * (x * (1 - 2 * φ) / ↑n + x * (1 + 2 * φ) / ↑n) = x / ↑n := by
    field_simp; ring
  have key : (1/2) * (Real.sqrt (x * (1 - 2 * φ)) * (1 - φ^2/2)^t +
    min (Real.sqrt (x * (1 + 2 * φ))) (Real.sqrt (↑n - x * (1 + 2 * φ))) * (1 - φ^2/2)^t)
    ≤ Real.sqrt x * ((1 - φ^2/2)^t * (1 - φ^2/2)) := by
    calc (1/2) * (Real.sqrt (x * (1 - 2 * φ)) * (1 - φ^2/2)^t +
      min (Real.sqrt (x * (1 + 2 * φ))) (Real.sqrt (↑n - x * (1 + 2 * φ))) * (1 - φ^2/2)^t)
      ≤ (1/2) * (Real.sqrt (x * (1 - 2 * φ)) * (1 - φ^2/2)^t +
        Real.sqrt (x * (1 + 2 * φ)) * (1 - φ^2/2)^t) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 1/2)
        linarith [mul_le_mul_of_nonneg_right hmin_add_le hc_nn]
      _ = (1 - φ^2/2)^t * ((1/2) * (Real.sqrt (x * (1 - 2 * φ)) +
        Real.sqrt (x * (1 + 2 * φ)))) := by ring
      _ = (1 - φ^2/2)^t * (Real.sqrt x * ((1/2) * (Real.sqrt (1 - 2 * φ) +
        Real.sqrt (1 + 2 * φ)))) := by
        rw [hsqrt_sub, hsqrt_add]; ring
      _ ≤ (1 - φ^2/2)^t * (Real.sqrt x * (1 - φ^2/2)) := by
        apply mul_le_mul_of_nonneg_left _ hc_nn
        exact mul_le_mul_of_nonneg_left (sqrt_midpoint_bound φ hφ hφ1) (Real.sqrt_nonneg x)
      _ = Real.sqrt x * ((1 - φ^2/2)^t * (1 - φ^2/2)) := by ring
  linarith

end LovaszSimonovits

namespace LovaszSimonovits

/--
[midpoint_bound_upper_proof](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LovaszSimonovits.lean)
-/
@[path]
lemma midpoint_bound_upper_proof
  {n : ℕ}
  {φ : ℝ}
-- given
  (hφ : 0 ≤ φ)
  (hφ1 : φ ≤ 1/2)
  (hn : 0 < n) :
-- imply
  MidpointBoundUpper n φ := by
-- proof
  intro t x hxm hxn
  simp only [lovaszSimonovitsBound]
  set y := (↑n : ℝ) - x with hy_def
  have hy0 : 0 ≤ y := by linarith
  have hym : y ≤ ↑n / 2 := by linarith
  have hx_ge_y : y ≤ x := by linarith
  have hmin_x : min (Real.sqrt x) (Real.sqrt (↑n - x)) = Real.sqrt (↑n - x) := by
    rw [show (↑n : ℝ) - x = y from by linarith]
    exact min_eq_right (Real.sqrt_le_sqrt hx_ge_y)
  have hrw1 : x - 2 * φ * (↑n - x) = ↑n - y * (1 + 2 * φ) := by linarith
  have hrw2 : x + 2 * φ * (↑n - x) = ↑n - y * (1 - 2 * φ) := by linarith
  have hrw3 : (↑n : ℝ) - (↑n - y * (1 + 2 * φ)) = y * (1 + 2 * φ) := by ring
  have hrw4 : (↑n : ℝ) - (↑n - y * (1 - 2 * φ)) = y * (1 - 2 * φ) := by ring
  rw [hrw1, hrw2, hrw3, hrw4]
  have hy_sub_le : y * (1 - 2 * φ) ≤ ↑n - y * (1 - 2 * φ) := by nlinarith
  have hmin_add : min (Real.sqrt (↑n - y * (1 - 2 * φ))) (Real.sqrt (y * (1 - 2 * φ))) =
    Real.sqrt (y * (1 - 2 * φ)) :=
    min_eq_right (Real.sqrt_le_sqrt hy_sub_le)
  have hmin_sub_le : min (Real.sqrt (↑n - y * (1 + 2 * φ))) (Real.sqrt (y * (1 + 2 * φ))) ≤
    Real.sqrt (y * (1 + 2 * φ)) := min_le_right _ _
  rw [hmin_add, hmin_x, show (↑n : ℝ) - x = y from by linarith]
  have hsqrt_sub : Real.sqrt (y * (1 - 2 * φ)) = Real.sqrt y * Real.sqrt (1 - 2 * φ) :=
    Real.sqrt_mul hy0 _
  have hsqrt_add : Real.sqrt (y * (1 + 2 * φ)) = Real.sqrt y * Real.sqrt (1 + 2 * φ) :=
    Real.sqrt_mul hy0 _
  have hc_nn : (0 : ℝ) ≤ (1 - φ^2 / 2)^t := pow_nonneg (by nlinarith [sq_nonneg φ]) _
  have hct : (1 - φ ^ 2 / 2) ^ (t + 1) = (1 - φ ^ 2 / 2) ^ t * (1 - φ ^ 2 / 2) := pow_succ _ _
  rw [hct]
  have hlinear : (1/2) * ((↑n - y * (1 + 2 * φ)) / ↑n + (↑n - y * (1 - 2 * φ)) / ↑n) =
    x / ↑n := by field_simp; linarith
  have key : (1/2) * (min (Real.sqrt (↑n - y * (1 + 2 * φ))) (Real.sqrt (y * (1 + 2 * φ))) *
    (1 - φ^2/2)^t + Real.sqrt (y * (1 - 2 * φ)) * (1 - φ^2/2)^t)
    ≤ Real.sqrt y * ((1 - φ^2/2)^t * (1 - φ^2/2)) := by
    calc (1/2) * (min (Real.sqrt (↑n - y * (1 + 2 * φ))) (Real.sqrt (y * (1 + 2 * φ))) *
      (1 - φ^2/2)^t + Real.sqrt (y * (1 - 2 * φ)) * (1 - φ^2/2)^t)
      ≤ (1/2) * (Real.sqrt (y * (1 + 2 * φ)) * (1 - φ^2/2)^t +
        Real.sqrt (y * (1 - 2 * φ)) * (1 - φ^2/2)^t) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 1/2)
        linarith [mul_le_mul_of_nonneg_right hmin_sub_le hc_nn]
      _ = (1 - φ^2/2)^t * ((1/2) * (Real.sqrt (y * (1 + 2 * φ)) +
        Real.sqrt (y * (1 - 2 * φ)))) := by ring
      _ = (1 - φ^2/2)^t * (Real.sqrt y * ((1/2) * (Real.sqrt (1 + 2 * φ) +
        Real.sqrt (1 - 2 * φ)))) := by
        rw [hsqrt_sub, hsqrt_add]; ring
      _ ≤ (1 - φ^2/2)^t * (Real.sqrt y * (1 - φ^2/2)) := by
        apply mul_le_mul_of_nonneg_left _ hc_nn
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg y)
        linarith [sqrt_midpoint_bound φ hφ hφ1]
      _ = Real.sqrt y * ((1 - φ^2/2)^t * (1 - φ^2/2)) := by ring
  linarith

end LovaszSimonovits

namespace LovaszSimonovits

/--
[lovasz_simonovits](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LovaszSimonovits.lean)
-/
@[path]
lemma lovasz_simonovits
  {n : ℕ}
  {ρ : ℕ → Fin n → ℝ}
  {φ : ℝ}
-- given
  (hφ : 0 ≤ φ)
  (hφ1 : φ ≤ 1/2)
  (hevol : SatisfiesEvolutionBound ρ φ)
  (hbase : ∀ x : ℝ, 0 ≤ x → x ≤ ↑n → lsCurve (ρ 0) x ≤ lovaszSimonovitsBound n φ 0 x)
  (hmid_lower : MidpointBoundLower n φ)
  (hmid_upper : MidpointBoundUpper n φ) :
-- imply
  ∀ t : ℕ, ∀ x : ℝ, 0 ≤ x → x ≤ ↑n → lsCurve (ρ t) x ≤ lovaszSimonovitsBound n φ t x := by
-- proof
  intro t
  induction t with
  | zero => exact hbase
  | succ t ih =>
    intro x hx0 hxn
    have hevol_step := hevol t x hx0 hxn
    split_ifs at hevol_step with hle
    ·
      have hx_sub_nn : 0 ≤ x - 2 * φ * x := by nlinarith
      have hx_sub_le : x - 2 * φ * x ≤ ↑n := by nlinarith
      have hx_add_nn : 0 ≤ x + 2 * φ * x := by nlinarith
      have hx_add_le : x + 2 * φ * x ≤ ↑n := by nlinarith
      calc lsCurve (ρ (t + 1)) x
        ≤ (1/2) * (lsCurve (ρ t) (x - 2 * φ * x) +
          lsCurve (ρ t) (x + 2 * φ * x)) := hevol_step
        _ ≤ (1/2) * (lovaszSimonovitsBound n φ t (x - 2 * φ * x) +
          lovaszSimonovitsBound n φ t (x + 2 * φ * x)) :=
          midpoint_mono_pointwise (ih _ hx_sub_nn hx_sub_le) (ih _ hx_add_nn hx_add_le)
        _ ≤ lovaszSimonovitsBound n φ (t + 1) x := hmid_lower t x hx0 hle
    ·
      have hle' : ↑n / 2 ≤ x := by linarith [not_le.mp hle]
      have hx_sub_nn : 0 ≤ x - 2 * φ * (↑n - x) := by nlinarith
      have hx_sub_le : x - 2 * φ * (↑n - x) ≤ ↑n := by nlinarith
      have hx_add_nn : 0 ≤ x + 2 * φ * (↑n - x) := by nlinarith
      have hx_add_le : x + 2 * φ * (↑n - x) ≤ ↑n := by nlinarith
      calc lsCurve (ρ (t + 1)) x
        ≤ (1/2) * (lsCurve (ρ t) (x - 2 * φ * (↑n - x)) +
          lsCurve (ρ t) (x + 2 * φ * (↑n - x))) := hevol_step
        _ ≤ (1/2) * (lovaszSimonovitsBound n φ t (x - 2 * φ * (↑n - x)) +
          lovaszSimonovitsBound n φ t (x + 2 * φ * (↑n - x))) :=
          midpoint_mono_pointwise (ih _ hx_sub_nn hx_sub_le) (ih _ hx_add_nn hx_add_le)
        _ ≤ lovaszSimonovitsBound n φ (t + 1) x := hmid_upper t x hle' hxn

end LovaszSimonovits

namespace LovaszSimonovits

/--
[lovasz_simonovits_full](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LovaszSimonovits.lean)
-/
@[path]
lemma lovasz_simonovits_full
  {n : ℕ}
  {ρ : ℕ → Fin n → ℝ}
  {φ : ℝ}
-- given
  (hn : 0 < n)
  (hφ : 0 ≤ φ)
  (hφ1 : φ ≤ 1/2)
  (hevol : SatisfiesEvolutionBound ρ φ)
  (hbase : ∀ x : ℝ, 0 ≤ x → x ≤ ↑n → lsCurve (ρ 0) x ≤ lovaszSimonovitsBound n φ 0 x) :
-- imply
  ∀ t : ℕ, ∀ x : ℝ, 0 ≤ x → x ≤ ↑n → lsCurve (ρ t) x ≤ lovaszSimonovitsBound n φ t x :=
-- proof
  lovasz_simonovits ρ φ hφ hφ1 hevol hbase
    (midpoint_bound_lower_proof n φ hφ hφ1 hn)
    (midpoint_bound_upper_proof n φ hφ hφ1 hn)

end LovaszSimonovits

namespace LovaszSimonovits

/--
[lovasz_simonovits_complement_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LovaszSimonovits.lean)
-/
@[path]
lemma lovasz_simonovits_complement_bound
  {n : ℕ}
  {φ : ℝ}
  {t : ℕ}
  {I_t : ℝ → ℝ}
  {x : ℝ}
-- given
  (hn : 0 < n)
  (hLS_nx : I_t (↑n - x) ≤ lovaszSimonovitsBound n φ t (↑n - x))
  (hcompl : I_t x + I_t (↑n - x) ≥ 1) :
-- imply
  x / ↑n ≤ I_t x + min (Real.sqrt x) (Real.sqrt (↑n - x)) * (1 - φ^2 / 2)^t := by
-- proof
  simp only [lovaszSimonovitsBound] at hLS_nx
  have hmin_eq : min (Real.sqrt (↑n - x)) (Real.sqrt (↑n - (↑n - x))) =
    min (Real.sqrt x) (Real.sqrt (↑n - x)) := by
    have : (↑n : ℝ) - (↑n - x) = x := by ring
    rw [this, min_comm]
  rw [hmin_eq] at hLS_nx
  have h2 : (↑n - x) / (↑n : ℝ) = 1 - x / ↑n := by field_simp
  linarith [h2]

end LovaszSimonovits

namespace LovaszSimonovits

/--
[corollary12](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LovaszSimonovits.lean)
-/
@[path]
lemma corollary12
  {n : ℕ}
  {φ : ℝ}
  {t : ℕ}
  {I_t : ℝ → ℝ}
  {x : ℝ}
-- given
  (_hx0 : 0 ≤ x)
  (_hxn : x ≤ ↑n)
  (hLS : I_t x ≤ lovaszSimonovitsBound n φ t x)
  (hLS_lower : x / ↑n ≤ I_t x + min (Real.sqrt x) (Real.sqrt (↑n - x)) * (1 - φ^2 / 2)^t) :
-- imply
  |I_t x - x / ↑n| ≤ min (Real.sqrt x) (Real.sqrt (↑n - x)) * (1 - φ^2 / 2)^t := by
-- proof
  rw [abs_le]
  constructor
  · linarith
  · unfold lovaszSimonovitsBound at hLS; linarith

end LovaszSimonovits

namespace LovaszSimonovits

/--
[corollary12_from_theorem11](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LovaszSimonovits.lean)
-/
@[path]
lemma corollary12_from_theorem11
  {n : ℕ}
  {φ : ℝ}
  {t : ℕ}
  {I_t : ℝ → ℝ}
  {x : ℝ}
-- given
  (hx0 : 0 ≤ x)
  (hxn : x ≤ ↑n)
  (hn : 0 < n)
  (hLS : I_t x ≤ lovaszSimonovitsBound n φ t x)
  (hLS_nx : I_t (↑n - x) ≤ lovaszSimonovitsBound n φ t (↑n - x))
  (hcompl : I_t x + I_t (↑n - x) ≥ 1) :
-- imply
  |I_t x - x / ↑n| ≤ min (Real.sqrt x) (Real.sqrt (↑n - x)) * (1 - φ^2 / 2)^t := by
-- proof
  have hlower := lovasz_simonovits_complement_bound φ t I_t x hn hLS_nx hcompl
  exact corollary12 φ t I_t x hx0 hxn hLS hlower

end LovaszSimonovits

namespace LovaszSimonovits

/--
[corollary12_vertex_set](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LovaszSimonovits.lean)
-/
@[path]
lemma corollary12_vertex_set
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : ℕ}
  {t : ℕ}
  {p_t : V → ℝ}
  {W : Finset V}
  {x : ℝ}
  {I_t : ℝ → ℝ}
-- given
  (_hx_vol : x = ↑(G.volume W))
  (_hn_vol : n = G.volume Finset.univ)
  (hx0 : 0 ≤ x)
  (hxn : x ≤ ↑n)
  (hn : 0 < n)
  (hmass : W.sum p_t = I_t x)
  (hLS : I_t x ≤ lovaszSimonovitsBound n (↑(G.conductance) : ℝ) t x)
  (hLS_nx : I_t (↑n - x) ≤ lovaszSimonovitsBound n (↑(G.conductance) : ℝ) t (↑n - x))
  (hcompl : I_t x + I_t (↑n - x) ≥ 1) :
-- imply
  |W.sum p_t - x / ↑n| ≤ min (Real.sqrt x) (Real.sqrt (↑n - x)) * (1 - (↑(G.conductance) : ℝ)^2 / 2)^t := by
-- proof
  rw [hmass]
  exact corollary12_from_theorem11 (↑(G.conductance) : ℝ) t I_t x hx0 hxn hn hLS hLS_nx hcompl

end LovaszSimonovits


-- created on 2026-10-23
