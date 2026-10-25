import Mathlib
import sympy.Basic
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter3.Def_3_10
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter3.Def_3_10


namespace Chapter3

/--
[sobolevCoeff_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Prop_3_12.lean)
-/
@[path]
lemma sobolevCoeff_mono
  {β β' : ℝ}
  {j : ℕ}
-- given
  (hβ' : 0 < β')
  (hββ' : β' ≤ β) :
-- imply
  sobolevCoeff β' j ≤ sobolevCoeff β j := by
-- proof
  unfold sobolevCoeff
  split
  · rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [Real.zero_rpow (ne_of_gt hβ'),
      Real.zero_rpow (ne_of_gt (lt_of_lt_of_le hβ' hββ'))]
    · exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hj) hββ'
  · rcases Nat.eq_zero_or_pos (j - 1) with h | hj
    · simp [h, Real.zero_rpow (ne_of_gt hβ'),
      Real.zero_rpow (ne_of_gt (lt_of_lt_of_le hβ' hββ'))]
    · exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hj) hββ'

end Chapter3

namespace Chapter3

/--
[sobolev_ellipsoid_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Prop_3_12.lean)
-/
@[path]
lemma sobolev_ellipsoid_monotone
  {M : ℕ}
  {β β' Q : ℝ}
-- given
  (hβ' : 0 < β')
  (hββ' : β' < β)
  (_hQ : 0 < Q) :
-- imply
  SobolevEllipsoid β Q M ⊆ SobolevEllipsoid β' Q M := by
-- proof
  intro θ hθ
  simp only [SobolevEllipsoid, Set.mem_setOf_eq] at hθ ⊢
  calc ∑ j : Fin M, (sobolevCoeff β' (j.val + 1)) ^ 2 * (θ j) ^ 2
    ≤ ∑ j : Fin M, (sobolevCoeff β (j.val + 1)) ^ 2 * (θ j) ^ 2 := by
      apply Finset.sum_le_sum; intro j _
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact pow_le_pow_left₀ (sobolevCoeff_nonneg (le_of_lt hβ') (j.val + 1))
        (sobolevCoeff_mono hβ' (le_of_lt hββ') (j.val + 1)) 2
    _ ≤ Q := hθ

end Chapter3

namespace Chapter3

/--
[sobolev_summable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Prop_3_12.lean)
-/
@[path]
lemma sobolev_summable
  {M : ℕ}
  {β Q : ℝ}
  {θ : Fin M → ℝ}
-- given
  (_hβ : 1/2 < β)
  (hQ : 0 < Q)
  (hθ : θ ∈ SobolevEllipsoid β Q M) :
-- imply
  (∑ j : Fin M, if sobolevCoeff β (j.val + 1) = 0 then 0 else |θ j|) ≤ Real.sqrt Q * Real.sqrt (∑ j : Fin M, if sobolevCoeff β (j.val + 1) = 0 then 0 else 1 / (sobolevCoeff β (j.val + 1)) ^ 2) := by
-- proof
  let a : Fin M → ℝ := fun j => sobolevCoeff β (j.val + 1)
  let S := ∑ j : Fin M, if a j = 0 then (0 : ℝ) else |θ j|
  let T := ∑ j : Fin M, if a j = 0 then (0 : ℝ) else 1 / (a j) ^ 2
  suffices h : S ^ 2 ≤ Q * T by
    have hS_nn : 0 ≤ S := Finset.sum_nonneg fun j _ => by split_ifs <;> positivity
    have hT_nn : 0 ≤ T := Finset.sum_nonneg fun j _ => by split_ifs <;> positivity
    rw [← Real.sqrt_mul (le_of_lt hQ) T]
    exact (Real.le_sqrt hS_nn (mul_nonneg (le_of_lt hQ) hT_nn)).mpr h
  have hS_eq : S = ∑ j : Fin M,
    (a j * |θ j|) * (if a j = 0 then 0 else 1 / a j) := by
    apply Finset.sum_congr rfl; intro j _
    split_ifs with h <;> simp [h]; field_simp
  rw [hS_eq]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun j => a j * |θ j|) (fun j => if a j = 0 then (0 : ℝ) else 1 / a j)
  have hf_eq : ∑ j : Fin M, (a j * |θ j|) ^ 2 =
    ∑ j : Fin M, a j ^ 2 * (θ j) ^ 2 := by
    apply Finset.sum_congr rfl; intro j _; rw [mul_pow, sq_abs]
  have hg_eq : ∑ j : Fin M,
    (if a j = 0 then (0 : ℝ) else 1 / a j) ^ 2 = T := by
    apply Finset.sum_congr rfl; intro j _
    split_ifs <;> simp [one_div, inv_pow]
  rw [hf_eq, hg_eq] at hCS
  exact le_trans hCS (mul_le_mul_of_nonneg_right hθ
    (Finset.sum_nonneg fun j _ => by split_ifs <;> positivity))

end Chapter3

namespace Chapter3

/--
[prop_3_12_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Prop_3_12.lean)
-/
@[path]
lemma prop_3_12_monotone
  {M : ℕ}
  {β β' Q : ℝ}
-- given
  (hβ' : 0 < β')
  (hββ' : β' < β)
  (hQ : 0 < Q) :
-- imply
  SobolevEllipsoid β Q M ⊆ SobolevEllipsoid β' Q M :=
-- proof
  sobolev_ellipsoid_monotone hβ' hββ' hQ

end Chapter3

namespace Chapter3

/--
[sobolevCoeff_ge_rpow_shift](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Prop_3_12.lean)
-/
@[path]
lemma sobolevCoeff_ge_rpow_shift
  {β : ℝ}
  {j : ℕ}
-- given
  (hβ : 0 < β) :
-- imply
  ((j + 1 : ℕ) : ℝ) ^ β ≤ sobolevCoeff β (j + 2) := by
-- proof
  unfold sobolevCoeff
  split
  · apply Real.rpow_le_rpow (Nat.cast_nonneg _)
    · exact_mod_cast (show (j + 1 : ℕ) ≤ j + 2 by omega)
    · exact le_of_lt hβ
  · have h : (j + 2 : ℕ) - 1 = j + 1 := by omega
    rw [h]

end Chapter3

namespace Chapter3

/--
[sobolevCoeff_pos_shift](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Prop_3_12.lean)
-/
@[path]
lemma sobolevCoeff_pos_shift
  {β : ℝ}
  {j : ℕ}
-- given
  (hβ : 0 < β) :
-- imply
  0 < sobolevCoeff β (j + 2) :=
-- proof
  lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < j + 1 by omega)) β)
    (sobolevCoeff_ge_rpow_shift hβ j)

end Chapter3

namespace Chapter3

/--
[prop_3_12_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Prop_3_12.lean)
-/
@[path]
lemma prop_3_12_continuous
  {β Q : ℝ}
  {θ : ℕ → ℝ}
-- given
  (hβ : 1/2 < β)
  (hQ : 0 < Q)
  (hθ : ∀ M, ∑ j ∈ Finset.range M, (sobolevCoeff β (j + 1))^2 * (θ j)^2 ≤ Q) :
-- imply
  Summable (fun j => ‖θ j‖) ∧ Continuous (fun x : ℝ => ∑' j, θ j * trigBasis (j + 1) x) := by
-- proof
  have hβ_pos : 0 < β := by linarith
  have hβ_ne : β ≠ 0 := ne_of_gt hβ_pos
  have hshifted : ∀ N, ∑ j ∈ Finset.range N,
    (sobolevCoeff β (j + 2))^2 * (θ (j + 1))^2 ≤ Q := by
    intro N
    have h := hθ (N + 1)
    rw [Finset.sum_range_succ'] at h
    simp only [sobolevCoeff_one hβ_ne, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_mul, add_zero] at h
    exact h
  have hT_summable : Summable (fun j : ℕ => (1 / sobolevCoeff β (j + 2))^2) := by
    apply Summable.of_nonneg_of_le (fun j => sq_nonneg _)
      (f := fun j : ℕ => (((j + 1 : ℕ) : ℝ) ^ β)⁻¹ ^ 2)
    · intro j
      apply pow_le_pow_left₀
        (div_nonneg zero_le_one (le_of_lt (sobolevCoeff_pos_shift hβ_pos j)))
      rwa [one_div]
        (Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < j + 1 by omega)) β)
        (sobolevCoeff_ge_rpow_shift hβ_pos j)
    · have key : ∀ j : ℕ, (((j + 1 : ℕ) : ℝ) ^ β)⁻¹ ^ 2 =
      (((j + 1 : ℕ) : ℝ) ^ (2 * β))⁻¹ := by
      intro j; rw [inv_pow, ← Real.rpow_natCast (((j + 1 : ℕ) : ℝ) ^ β) 2,
        ← Real.rpow_mul (Nat.cast_nonneg _)]; ring_nf
      simp_rw [key]
      exact (summable_nat_add_iff
        (f := fun n : ℕ => ((n : ℝ) ^ (2 * β))⁻¹) 1).mpr
        (Real.summable_nat_rpow_inv.mpr (by linarith))
  set T := ∑' j, (1 / sobolevCoeff β (j + 2))^2
  have hsum_shifted : Summable (fun j => ‖θ (j + 1)‖) := by
    apply summable_of_sum_range_le (fun j => norm_nonneg _)
      (c := Real.sqrt Q * Real.sqrt T)
    intro N; simp only [Real.norm_eq_abs]
    have heq : ∑ j ∈ Finset.range N, |θ (j + 1)| =
      ∑ j ∈ Finset.range N,
        (sobolevCoeff β (j + 2) * |θ (j + 1)|) *
          (1 / sobolevCoeff β (j + 2)) := by
      apply Finset.sum_congr rfl; intro j _
      field_simp [ne_of_gt (sobolevCoeff_pos_shift hβ_pos j)]
    rw [heq]
    calc ∑ j ∈ Finset.range N,
      (sobolevCoeff β (j + 2) * |θ (j + 1)|) *
        (1 / sobolevCoeff β (j + 2))
      ≤ Real.sqrt (∑ j ∈ Finset.range N,
        (sobolevCoeff β (j + 2) * |θ (j + 1)|) ^ 2) *
        Real.sqrt (∑ j ∈ Finset.range N,
          (1 / sobolevCoeff β (j + 2)) ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ ≤ Real.sqrt Q * Real.sqrt T := by
        apply mul_le_mul
        · apply Real.sqrt_le_sqrt
          simp_rw [mul_pow, sq_abs]
          exact hshifted N
        · apply Real.sqrt_le_sqrt
          exact hT_summable.sum_le_tsum _ (fun j _ => sq_nonneg _)
        · exact Real.sqrt_nonneg _
        · exact Real.sqrt_nonneg _
  have hsum : Summable (fun j => ‖θ j‖) :=
    (summable_nat_add_iff 1).mp hsum_shifted
  have hcont : Continuous (fun x : ℝ => ∑' j, θ j * trigBasis (j + 1) x) := by
    apply continuous_tsum
      (f := fun j x => θ j * trigBasis (j + 1) x)
      (u := fun j => ‖θ j‖ * Real.sqrt 2)
    · intro j
      exact Continuous.mul continuous_const
        (by unfold trigBasis; split_ifs <;> fun_prop)
    · exact hsum.mul_right _
    · intro j x; simp only [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (trigBasis_bounded _ _) (abs_nonneg _)
  exact ⟨hsum, hcont⟩

end Chapter3

namespace Chapter3

/--
[prop_3_12](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Prop_3_12.lean)
-/
@[path]
lemma prop_3_12
-- imply
  (∀ {M : ℕ} {β β' Q : ℝ}, 0 < β' → β' < β → 0 < Q → SobolevEllipsoid β Q M ⊆ SobolevEllipsoid β' Q M) ∧ (∀ {β Q : ℝ}, 1/2 < β → 0 < Q → ∀ (θ : ℕ → ℝ), (∀ M, ∑ j ∈ Finset.range M, (sobolevCoeff β (j + 1))^2 * (θ j)^2 ≤ Q) → Summable (fun j => ‖θ j‖) ∧ Continuous (fun x : ℝ => ∑' j, θ j * trigBasis (j + 1) x)) :=
-- proof
  ⟨fun hβ' hββ' hQ => prop_3_12_monotone hβ' hββ' hQ,
    fun hβ hQ θ hθ => prop_3_12_continuous hβ hQ θ hθ⟩

end Chapter3


-- created on 2026-10-23
