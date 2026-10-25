import Mathlib
import sympy.Basic
import Def.v1.Atlas.BooleanFunctions.code.UncoveredTargets
open Finset BigOperators BooleanFourier


namespace BooleanFourier

/--
[parseval_pm_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/UncoveredTargets.lean)
-/
@[path]
lemma parseval_pm_one
  {n : ℕ}
  {f : (Fin n → Bool) → ℝ}
-- given
  (hf : ∀ x, f x = 1 ∨ f x = -1) :
-- imply
  ∑ S : Finset (Fin n), (fourierCoeff f S) ^ 2 = 1 := by
-- proof
  have hpars := parseval f
  rw [hpars]
  have hfsq : ∀ x : Fin n → Bool, (f x) ^ 2 = 1 := by
    intro x
    obtain h | h <;> simp [h] := hf x
  simp_rw [hfsq, Finset.sum_const, Finset.card_univ, Fintype.card_pi,
    Fintype.card_bool, Finset.prod_const, Finset.card_fin]
  simp [Nat.cast_pow, Nat.cast_ofNat]

end BooleanFourier

namespace BooleanFourier

/--
[variance_pm_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/UncoveredTargets.lean)
-/
@[path]
lemma variance_pm_one
  {n : ℕ}
  {f : (Fin n → Bool) → ℝ}
-- given
  (hf : ∀ x, f x = 1 ∨ f x = -1) :
-- imply
  ∑ S ∈ (univ : Finset (Finset (Fin n))).filter (· ≠ ∅), (fourierCoeff f S) ^ 2 = 1 - (fourierCoeff f ∅) ^ 2 := by
-- proof
  have hpars := parseval_pm_one f hf
  have hsplit : ∑ S : Finset (Fin n), (fourierCoeff f S) ^ 2 =
    (fourierCoeff f ∅) ^ 2 +
    ∑ S ∈ (univ : Finset (Finset (Fin n))).filter (· ≠ ∅),
      (fourierCoeff f S) ^ 2 := by
    rw [← Finset.add_sum_erase (univ : Finset (Finset (Fin n)))
      (fun S => (fourierCoeff f S) ^ 2) (Finset.mem_univ ∅)]
    congr 1
    apply Finset.sum_congr
    · ext S; simp [Finset.mem_erase]
    · intros; rfl
  linarith

end BooleanFourier

namespace BooleanFourier

/--
[totalInfluence_eq_weighted_degree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/UncoveredTargets.lean)
-/
@[path]
lemma totalInfluence_eq_weighted_degree
  {n : ℕ}
  {f : (Fin n → Bool) → ℝ} :
-- imply
  ∑ S : Finset (Fin n), (S.card : ℝ) * (fourierCoeff f S) ^ 2 = ∑ k ∈ Finset.range (n + 1), (k : ℝ) * fourierWeightAtLevel k f := by
-- proof
  classical
  unfold fourierWeightAtLevel
  simp_rw [Finset.mul_sum]
  have hpart : (univ : Finset (Finset (Fin n))) =
    (Finset.range (n + 1)).biUnion (fun k =>
      (univ : Finset (Finset (Fin n))).filter (fun S => S.card = k)) := by
    ext S
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro _
      have hle : S.card ≤ n := by
        have := Finset.card_le_univ S
        simp [Fintype.card_fin] at this
        exact this
      exact ⟨S.card, Nat.lt_succ_of_le hle, rfl⟩
    · intro _; exact trivial
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range (n + 1)))
    (fun k => (univ : Finset (Finset (Fin n))).filter (fun S => S.card = k)) := by
    intro i _ j _ hij
    simp only [Finset.disjoint_filter]
    intro S _ hSi hSj
    exact absurd (hSi ▸ hSj) hij
  conv_lhs => rw [hpart, Finset.sum_biUnion hdisj]
  congr 1
  ext k
  apply Finset.sum_congr rfl
  intro S hS
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
  rw [hS]

end BooleanFourier

namespace BooleanFourier

/--
[low_degree_concentration](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/UncoveredTargets.lean)
-/
@[path]
lemma low_degree_concentration
  {n : ℕ}
  {f : (Fin n → Bool) → ℝ}
  {K : ℝ}
  {ε : ℝ}
-- given
  (hf : ∀ x, f x = 1 ∨ f x = -1)
  (hK : (∑ S : Finset (Fin n), (S.card : ℝ) * (fourierCoeff f S) ^ 2) ≤ K)
  (hε : 0 < ε) :
-- imply
  ∑ S ∈ (univ : Finset (Finset (Fin n))).filter (fun S => (S.card : ℝ) > 2 * K / ε), (fourierCoeff f S) ^ 2 ≤ ε := by
-- proof
  have h_nonneg_term : ∀ S : Finset (Fin n), 0 ≤ (S.card : ℝ) * (fourierCoeff f S) ^ 2 :=
    fun S => mul_nonneg (by positivity) (sq_nonneg _)
  by_cases hK0 : K ≤ 0
  ·
    have hsum_nonneg : (0 : ℝ) ≤ ∑ S : Finset (Fin n), (S.card : ℝ) * (fourierCoeff f S) ^ 2 :=
      Finset.sum_nonneg fun S _ => h_nonneg_term S
    have hK_eq_zero : K = 0 := le_antisymm hK0 (le_trans hsum_nonneg hK)
    have hsum_zero : ∑ S : Finset (Fin n), (S.card : ℝ) * (fourierCoeff f S) ^ 2 = 0 :=
      le_antisymm (hK.trans hK0) hsum_nonneg
    have hterms : ∀ S ∈ (univ : Finset (Finset (Fin n))).filter
      (fun S => (S.card : ℝ) > 2 * K / ε), (fourierCoeff f S) ^ 2 = 0 := by
      intro S hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
      rw [hK_eq_zero] at hS
      simp only [mul_zero, zero_div] at hS
      have hScard_pos : 0 < S.card := by exact_mod_cast hS
      have hScard_ne : S.card ≠ 0 := Nat.pos_iff_ne_zero.mp hScard_pos
      have h_all_zero := (Finset.sum_eq_zero_iff_of_nonneg
        (fun S (_ : S ∈ Finset.univ) => h_nonneg_term S)).mp hsum_zero
      have h_term_zero := h_all_zero S (Finset.mem_univ S)
      have hScard_ne_real : (S.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hScard_ne
      exact (mul_eq_zero.mp h_term_zero).resolve_left hScard_ne_real
    calc ∑ S ∈ (univ : Finset (Finset (Fin n))).filter
      (fun S => (S.card : ℝ) > 2 * K / ε), (fourierCoeff f S) ^ 2
      = 0 := Finset.sum_eq_zero hterms
      _ ≤ ε := le_of_lt hε
  ·
    push_neg at hK0
    have hM_pos : (0 : ℝ) < 2 * K / ε := by positivity
    calc ∑ S ∈ (univ : Finset (Finset (Fin n))).filter
      (fun S => (S.card : ℝ) > 2 * K / ε), (fourierCoeff f S) ^ 2
      ≤ ∑ S ∈ (univ : Finset (Finset (Fin n))).filter
        (fun S => (S.card : ℝ) > 2 * K / ε),
        ((S.card : ℝ) / (2 * K / ε)) * (fourierCoeff f S) ^ 2 := by
        apply Finset.sum_le_sum
        intro S hS
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
        have h1 : (1 : ℝ) ≤ (S.card : ℝ) / (2 * K / ε) := by
          rw [le_div_iff₀ hM_pos]
          linarith
        nlinarith [sq_nonneg (fourierCoeff f S)]
      _ = (ε / (2 * K)) * ∑ S ∈ (univ : Finset (Finset (Fin n))).filter
        (fun S => (S.card : ℝ) > 2 * K / ε),
        (S.card : ℝ) * (fourierCoeff f S) ^ 2 := by
        rw [Finset.mul_sum]; congr 1; ext S; field_simp
      _ ≤ (ε / (2 * K)) * ∑ S : Finset (Fin n),
        (S.card : ℝ) * (fourierCoeff f S) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro S hS
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
          exact Finset.mem_univ S
        · intro S _ _
          exact h_nonneg_term S
      _ ≤ (ε / (2 * K)) * K := by
        apply mul_le_mul_of_nonneg_left hK (by positivity)
      _ = ε / 2 := by field_simp
      _ ≤ ε := by linarith

end BooleanFourier

namespace BooleanFourier

/--
[noiseStability_via_weight](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/UncoveredTargets.lean)
-/
@[path]
lemma noiseStability_via_weight
  {n : ℕ}
  {ρ : ℝ}
  {f : (Fin n → Bool) → ℝ} :
-- imply
  ∑ S : Finset (Fin n), ρ ^ S.card * (fourierCoeff f S) ^ 2 = ∑ k ∈ Finset.range (n + 1), ρ ^ k * fourierWeightAtLevel k f := by
-- proof
  classical
  unfold fourierWeightAtLevel
  simp_rw [Finset.mul_sum]
  have hpart : (univ : Finset (Finset (Fin n))) =
    (Finset.range (n + 1)).biUnion (fun k =>
      (univ : Finset (Finset (Fin n))).filter (fun S => S.card = k)) := by
    ext S
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro _
      have hle : S.card ≤ n := by
        have := Finset.card_le_univ S
        simp [Fintype.card_fin] at this
        exact this
      exact ⟨S.card, Nat.lt_succ_of_le hle, rfl⟩
    · intro _; exact trivial
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range (n + 1)))
    (fun k => (univ : Finset (Finset (Fin n))).filter (fun S => S.card = k)) := by
    intro i _ j _ hij
    simp only [Finset.disjoint_filter]
    intro S _ hSi hSj
    exact absurd (hSi ▸ hSj) hij
  conv_lhs => rw [hpart, Finset.sum_biUnion hdisj]
  congr 1
  ext k
  apply Finset.sum_congr rfl
  intro S hS
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
  rw [hS]

end BooleanFourier

namespace BooleanFourier

/--
[level_k_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/UncoveredTargets.lean)
-/
@[path]
lemma level_k_inequality
  {n : ℕ}
  {ρ : ℝ}
  {k : ℕ}
  {f : (Fin n → Bool) → ℝ}
-- given
  (hρ : |ρ| ≤ 1) :
-- imply
  fourierWeightUpToLevel k (noiseOperator ρ f) ≤ fourierWeightUpToLevel k f := by
-- proof
  unfold fourierWeightUpToLevel
  apply Finset.sum_le_sum
  intro S _
  rw [fourierCoeff_noiseOperator, mul_pow]
  have hρpow : (ρ ^ S.card) ^ 2 ≤ 1 := by
    have h1 : ρ ^ 2 ≤ 1 := by
      have := sq_abs ρ
      nlinarith [abs_nonneg ρ, sq_nonneg (|ρ|), sq_nonneg (|ρ| - 1)]
    have h2 : 0 ≤ ρ ^ 2 := sq_nonneg ρ
    calc (ρ ^ S.card) ^ 2 = (ρ ^ 2) ^ S.card := by ring
    _ ≤ 1 ^ S.card := by gcongr
    _ = 1 := one_pow _
  nlinarith [sq_nonneg (fourierCoeff f S)]

end BooleanFourier

namespace BooleanFourier

/--
[noiseOp_self_adjoint](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/UncoveredTargets.lean)
-/
@[path]
lemma noiseOp_self_adjoint
  {n : ℕ}
  {ρ : ℝ}
  {f g : (Fin n → Bool) → ℝ} :
-- imply
  innerProduct (noiseOperator ρ f) g = innerProduct f (noiseOperator ρ g) := by
-- proof
  have hlhs := plancherel (noiseOperator ρ f) g
  have hrhs := plancherel f (noiseOperator ρ g)
  rw [← hlhs, ← hrhs]
  congr 1
  ext S
  rw [fourierCoeff_noiseOperator, fourierCoeff_noiseOperator]
  ring

end BooleanFourier


-- created on 2026-10-23
