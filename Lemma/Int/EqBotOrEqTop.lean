import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[IsDiscreteValuationRing_subalgebra_eq_bot_or_eq_top](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsDiscreteValuationRing_subalgebra_eq_bot_or_eq_top.lean)
-/
@[path]
private lemma main
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  (S : Subalgebra R K) :
  -- imply
  S = ⊥ ∨ S = ⊤ := by
  -- proof
  classical
  if h : S ≤ ⊥ then
    apply Or.inl (le_antisymm h bot_le)
  else
    right
    obtain ⟨x, hxS, hxbot⟩ := Set.not_subset.mp h
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
    have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
    have hne : ∀ {r : R}, r ≠ 0 → algebraMap R K r ≠ 0 := fun hr h0 => hr (hinj (h0.trans (map_zero _).symm))
    have hϖ0 : algebraMap R K ϖ ≠ 0 := hne hϖ.ne_zero
    have hinv : (algebraMap R K ϖ)⁻¹ ∈ S := by
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
      have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
      have ha0 : a ≠ 0 := by
        rintro rfl
        apply hxbot
        rw [map_zero, zero_div]
        apply Subalgebra.zero_mem _
      obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
      obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
      have hB : algebraMap R K ((v : R) * ϖ ^ n) ≠ 0 := hne hb0
      have hmn : m < n := by
        by_contra hle
        push Not at hle
        apply hxbot
        rw [SetLike.mem_coe, Algebra.mem_bot]
        refine ⟨(u : R) * ((v⁻¹ : Units R) : R) * ϖ ^ (m - n), ?_⟩
        rw [eq_div_iff hB, ← map_mul]
        congr 1
        calc
          _ = (u : R) * (((v⁻¹ : Units R) : R) * (v : R)) * (ϖ ^ (m - n) * ϖ ^ n) := by ring
          _ = (u : R) * ϖ ^ m := by rw [Units.inv_mul, mul_one, ← pow_add, Nat.sub_add_cancel hle]
      set c : R := (v : R) * ((u⁻¹ : Units R) : R) * ϖ ^ (n - m - 1) with hc
      have key : algebraMap R K ϖ * (algebraMap R K c * algebraMap R K ((u : R) * ϖ ^ m)) = algebraMap R K ((v : R) * ϖ ^ n) := by
        rw [← map_mul, ← map_mul]
        congr 1
        calc
          _ = (v : R) * (((u⁻¹ : Units R) : R) * (u : R)) * (ϖ ^ 1 * ϖ ^ (n - m - 1) * ϖ ^ m) := by ring
          _ = (v : R) * ϖ ^ n := by
            rw [Units.inv_mul, mul_one, ← pow_add, ← pow_add]
            congr 2
            omega
      have key' : algebraMap R K c * algebraMap R K ((u : R) * ϖ ^ m) = (algebraMap R K ϖ)⁻¹ * algebraMap R K ((v : R) * ϖ ^ n) := (eq_inv_mul_iff_mul_eq₀ hϖ0).mpr key
      have : (algebraMap R K ϖ)⁻¹ = algebraMap R K c * (algebraMap R K ((u : R) * ϖ ^ m) / algebraMap R K ((v : R) * ϖ ^ n)) := by
        rw [← mul_div_assoc, key', mul_div_cancel_right₀ _ hB]
      rw [this]
      apply S.mul_mem (S.algebraMap_mem c) hxS
    rw [eq_top_iff]
    rintro y -
    obtain ⟨c, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := R) y
    obtain ⟨e, w, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hd) hϖ
    have hB : algebraMap R K ((w : R) * ϖ ^ e) ≠ 0 := hne (nonZeroDivisors.ne_zero hd)
    have : algebraMap R K c / algebraMap R K ((w : R) * ϖ ^ e) = algebraMap R K (c * ((w⁻¹ : Units R) : R)) * ((algebraMap R K ϖ)⁻¹) ^ e := by
      rw [div_eq_iff hB, map_mul, map_mul, map_pow, inv_pow]
      symm
      calc
        _ = algebraMap R K c * (algebraMap R K ((w⁻¹ : Units R) : R) * algebraMap R K (w : R)) * ((algebraMap R K ϖ ^ e)⁻¹ * algebraMap R K ϖ ^ e) := by ring
        _ = algebraMap R K c := by rw [← map_mul, Units.inv_mul, map_one, mul_one, inv_mul_cancel₀ (pow_ne_zero _ hϖ0), mul_one]
    rw [this]
    apply S.mul_mem (S.algebraMap_mem _) (S.pow_mem hinv e)


-- created on 2026-10-20
