import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.ProjectionTheory.code.LinnikLargeSieve
open Finset Complex LinnikLargeSieve


namespace LinnikLargeSieve

/--
[fareySet_range](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/LinnikLargeSieve.lean)
-/
@[path]
lemma fareySet_range
  {M : ℕ} :
-- imply
  ∀ x ∈ fareySet M, 0 ≤ x ∧ x < 1 := by
-- proof
  intro x hx
  simp only [fareySet, mem_biUnion, mem_image, Finset.mem_Icc] at hx
  obtain ⟨p, hp_mem, α, ⟨hα_lo, hα_hi⟩, rfl⟩ := hx
  simp only [primesInRange, mem_filter, Finset.mem_Icc] at hp_mem
  have hp_prime := hp_mem.2
  have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp_prime.pos
  constructor
  · exact div_nonneg (by positivity) hp_pos.le
  · rw [div_lt_one hp_pos]
    exact_mod_cast Nat.lt_of_le_of_lt hα_hi (Nat.sub_lt hp_prime.pos Nat.one_pos)

end LinnikLargeSieve

namespace LinnikLargeSieve

/--
[fareySet_separated](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/LinnikLargeSieve.lean)
-/
@[path]
lemma fareySet_separated
  {M : ℕ} :
-- imply
  ∀ x ∈ fareySet M, ∀ y ∈ fareySet M, x ≠ y → (1 : ℝ) / (M ^ 2 : ℝ) ≤ := by
-- proof
  intro x hx y hy hxy
  simp only [fareySet, mem_biUnion, mem_image, Finset.mem_Icc, primesInRange, mem_filter] at hx hy
  obtain ⟨p₁, ⟨hp₁_range, hp₁_prime⟩, α₁, ⟨hα₁_lo, hα₁_hi⟩, hx_eq⟩ := hx
  obtain ⟨p₂, ⟨hp₂_range, hp₂_prime⟩, α₂, ⟨hα₂_lo, hα₂_hi⟩, hy_eq⟩ := hy
  subst hx_eq; subst hy_eq
  have hp₁_pos : (0 : ℝ) < p₁ := Nat.cast_pos.mpr hp₁_prime.pos
  have hp₂_pos : (0 : ℝ) < p₂ := Nat.cast_pos.mpr hp₂_prime.pos
  have hM₁ : p₁ ≤ M := hp₁_range.2
  have hM₂ : p₂ ≤ M := hp₂_range.2
  have hdiff : (α₁ : ℝ) / p₁ - (α₂ : ℝ) / p₂ =
    ((α₁ : ℝ) * p₂ - (α₂ : ℝ) * p₁) / (p₁ * p₂) := by field_simp
  rw [hdiff]
  have hnum_ne : (α₁ : ℤ) * p₂ - (α₂ : ℤ) * p₁ ≠ 0 := by
    intro h
    apply hxy
    have h2 : (α₁ : ℝ) * p₂ = (α₂ : ℝ) * p₁ := by
      have : ((α₁ : ℤ) * (p₂ : ℤ) : ℤ) = ((α₂ : ℤ) * (p₁ : ℤ) : ℤ) := by omega
      exact_mod_cast this
    field_simp; linarith
  have hnum_abs : (1 : ℝ) ≤ |((α₁ : ℝ) * (p₂ : ℝ) - (α₂ : ℝ) * (p₁ : ℝ))| := by
    have h1 : (1 : ℤ) ≤ |((α₁ : ℤ) * p₂ - (α₂ : ℤ) * p₁)| := Int.one_le_abs hnum_ne
    exact_mod_cast h1
  have hprod_le : (p₁ : ℝ) * p₂ ≤ (M : ℝ) ^ 2 := by
    have h : (p₁ * p₂ : ℕ) ≤ M ^ 2 := by
      calc p₁ * p₂ ≤ M * M := Nat.mul_le_mul hM₁ hM₂
        _ = M ^ 2 := (Nat.pow_two M).symm
    exact_mod_cast h
  have hprod_pos : (0 : ℝ) < (p₁ : ℝ) * p₂ := mul_pos hp₁_pos hp₂_pos
  have hM_pos : (0 : ℕ) < M := Nat.pos_of_ne_zero (by
    intro hM0; subst hM0; exact absurd (Nat.le_zero.mp hM₁) (Nat.Prime.ne_zero hp₁_prime))
  have hM2_pos : (0 : ℝ) < (M : ℝ) ^ 2 := by positivity
  rw [abs_div, abs_of_pos hprod_pos]
  rw [div_le_div_iff₀ hM2_pos hprod_pos, one_mul]
  calc (p₁ : ℝ) * p₂ ≤ (M : ℝ) ^ 2 := hprod_le
    _ = 1 * (M : ℝ) ^ 2 := (one_mul _).symm
    _ ≤ |((α₁ : ℝ) * (p₂ : ℝ) - (α₂ : ℝ) * (p₁ : ℝ))| * (M : ℝ) ^ 2 := by gcongr

end LinnikLargeSieve

namespace LinnikLargeSieve

/--
[fareySet_pairwiseDisjoint](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/LinnikLargeSieve.lean)
-/
@[path]
lemma fareySet_pairwiseDisjoint
  {M : ℕ} :
-- imply
  (↑(primesInRange M) : Set ℕ).PairwiseDisjoint fun p => (Finset.Icc 1 (p - 1)).image fun (α : ℕ) => (α : ℝ) / (p : ℝ) := by
-- proof
  intro p₁ hp₁ p₂ hp₂ hne
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  simp only [mem_image, Finset.mem_Icc] at hx₁ hx₂
  obtain ⟨α₁, ⟨hα₁_lo, hα₁_hi⟩, hx₁_eq⟩ := hx₁
  obtain ⟨α₂, ⟨hα₂_lo, hα₂_hi⟩, hx₂_eq⟩ := hx₂
  have hp₁_prime : Nat.Prime p₁ := by
    simp only [primesInRange, mem_coe, mem_filter, Finset.mem_Icc] at hp₁; exact hp₁.2
  have hp₂_prime : Nat.Prime p₂ := by
    simp only [primesInRange, mem_coe, mem_filter, Finset.mem_Icc] at hp₂; exact hp₂.2
  have hp₁_pos : (0 : ℝ) < ↑p₁ := Nat.cast_pos.mpr hp₁_prime.pos
  have hp₂_pos : (0 : ℝ) < ↑p₂ := Nat.cast_pos.mpr hp₂_prime.pos
  have heq : (↑α₁ : ℝ) * ↑p₂ = (↑α₂ : ℝ) * ↑p₁ := by
    have h : (↑α₁ : ℝ) / ↑p₁ = (↑α₂ : ℝ) / ↑p₂ := by linarith
    field_simp at h; linarith
  have heq3 : α₁ * p₂ = α₂ * p₁ := by exact_mod_cast heq
  have hdvd : p₁ ∣ α₁ := by
    have h : p₁ ∣ α₁ * p₂ := ⟨α₂, by linarith⟩
    obtain h | h := hp₁_prime.dvd_mul.mp h
    · exact h
    · exfalso
      obtain rfl | rfl := hp₂_prime.eq_one_or_self_of_dvd p₁ h
      · linarith [hp₁_prime.one_lt]
      · exact hne rfl
  exact absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)

end LinnikLargeSieve

namespace LinnikLargeSieve

/--
[sum_over_fareySet](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/LinnikLargeSieve.lean)
-/
@[path]
lemma sum_over_fareySet
  {M : ℕ}
  {g : ℝ → ℝ} :
-- imply
  ∑ ξ ∈ fareySet M, g ξ = ∑ p ∈ primesInRange M, ∑ α ∈ Finset.Icc 1 (p - 1), g ((↑α : ℝ) / (↑p : ℝ)) := by
-- proof
  unfold fareySet
  rw [Finset.sum_biUnion (fareySet_pairwiseDisjoint M)]
  congr 1; ext p
  apply Finset.sum_image
  intro α₁ hα₁ α₂ _ heq
  have hα₁' := Finset.mem_Icc.mp hα₁
  have hp_pos : (0 : ℝ) < (↑p : ℝ) := by exact_mod_cast (show 0 < p by omega)
  exact_mod_cast (div_left_inj' (ne_of_gt hp_pos)).mp heq
/-- Reduction step: there exists a `1/M^2`-separated set `S ⊆ [0, 1)` (namely the Farey set
`Q_M`) such that
`linnikLHS N M f ≤ (2/M) ∑_{ξ ∈ S} |\widehat{f_H}(ξ)|²`. -/
end LinnikLargeSieve



-- created on 2026-10-23
