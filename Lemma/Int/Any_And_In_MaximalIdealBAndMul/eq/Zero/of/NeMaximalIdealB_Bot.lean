import Mathlib
import sympy.Basic


/--
[IsArtinianRing_exists_ne_zero_mem_maximalIdeal_forall_mul_eq_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsArtinianRing_exists_ne_zero_mem_maximalIdeal_forall_mul_eq_zero.lean)
-/
@[main]
private lemma main
  [CommRing B] [IsLocalRing B] [IsArtinianRing B]
-- given
  (h : IsLocalRing.maximalIdeal B ≠ ⊥) :
-- imply
  ∃ t : B, t ≠ 0 ∧ t ∈ IsLocalRing.maximalIdeal B ∧ ∀ m ∈ IsLocalRing.maximalIdeal B, m * t = 0 := by
-- proof
  classical

  obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := B)
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hN

  have hex : ∃ n, IsLocalRing.maximalIdeal B ^ n = ⊥ := ⟨N, hN⟩
  let n := Nat.find hex
  have hn : IsLocalRing.maximalIdeal B ^ n = ⊥ := Nat.find_spec hex
  have hn0 : n ≠ 0 := by
    intro h0
    have : IsLocalRing.maximalIdeal B ^ 0 = ⊥ := by rw [← h0]; exact hn
    rw [pow_zero, Ideal.one_eq_top] at this
    exact h (eq_bot_iff.mpr (this ▸ le_top))
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hlt : ¬ IsLocalRing.maximalIdeal B ^ m = ⊥ := Nat.find_min hex (by omega)

  obtain ⟨t, htm, ht0⟩ : ∃ t ∈ IsLocalRing.maximalIdeal B ^ m, t ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hlt (eq_bot_iff.mpr fun x hx => (Submodule.mem_bot B).mpr (by simpa using hcon x hx))
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0, zero_add] at hm
    rw [hm, pow_one] at hn
    exact h hn
  refine ⟨t, ht0, ?_, fun x hx => ?_⟩
  · exact Ideal.pow_le_self hm0 htm
  · have : x * t ∈ IsLocalRing.maximalIdeal B ^ n := by
      rw [hm, pow_succ']
      exact Ideal.mul_mem_mul hx htm
    rw [hn] at this
    exact (Submodule.mem_bot B).mp this


-- created on 2026-10-05
