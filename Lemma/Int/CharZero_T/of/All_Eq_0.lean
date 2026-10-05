import Mathlib
import sympy.Basic


/--
[DeligneSerre_charZero_quotient](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_DeligneSerre_charZero_quotient.lean)
-/
@[main]
private lemma main
  [CommRing T]
  {𝔭 : Ideal T}
-- given
  (h𝔭 : ∀ (n : ℤ), (algebraMap ℤ T) n ∈ 𝔭 → n = 0) :
-- imply
  CharZero (T ⧸ 𝔭) := by
-- proof
  refine ⟨fun m n hmn => ?_⟩
  have h : algebraMap ℤ T ((m : ℤ) - (n : ℤ)) ∈ 𝔭 := by
    rw [map_sub]
    have hcast : ∀ k : ℕ, (Ideal.Quotient.mk 𝔭) (algebraMap ℤ T (k : ℤ)) = (k : T ⧸ 𝔭) := by
      intro k; push_cast; simp
    have hm : (Ideal.Quotient.mk 𝔭) (algebraMap ℤ T (m : ℤ)) =
        (Ideal.Quotient.mk 𝔭) (algebraMap ℤ T (n : ℤ)) := by
      rw [hcast m, hcast n, hmn]
    rwa [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem] at hm
  have := h𝔭 _ h
  omega


-- created on 2026-10-05
