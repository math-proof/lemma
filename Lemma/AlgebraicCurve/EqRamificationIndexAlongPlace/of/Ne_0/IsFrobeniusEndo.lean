import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_AlgebraicCurve_FrobeniusEndo
import Lemma.P2M.Util

open AlgebraicCurve

/--
[AlgebraicCurve_IsFrobeniusEndo_ramificationIndexAlong_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_IsFrobeniusEndo_ramificationIndexAlong_eq.lean)
-/

private theorem Place.ord_pow' {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : AlgebraicCurve.Place K F) (f : F) (n : ℕ) :
    v.ord (f ^ n) = n * v.ord f := by
  have := v.ord_zpow f (n : ℤ)
  rwa [zpow_natCast] at this
@[path]
private lemma main
  {K F : Type*} [Field K] [Field F] [Algebra K F]
  {φ : F →ₐ[K] F}
  {ℓ : ℕ}
  {w : AlgebraicCurve.Place K F}
-- given
  (h : AlgebraicCurve.IsFrobeniusEndo ℓ φ)
  (hℓ : ℓ ≠ 0) :
-- imply
  AlgebraicCurve.Place.ramificationIndexAlong φ w = ℓ := by
-- proof
  let := AlgebraicCurve.algebraAlong φ
  show w.ramificationIndex F = ℓ
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  have hπF : (π : F) ≠ 0 := by
    simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  obtain ⟨y, hy⟩ := h.pow_mem_range (π : F)
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hy
    exact pow_ne_zero ℓ hπF hy.symm
  have hyord : w.ord (algebraMap F F y) = (ℓ : ℤ) := by
    show w.ord (φ y) = (ℓ : ℤ)
    rw [hy, Place.ord_pow' w, w.ord_coe_irreducible hπ, mul_one]
  have hℓmem : ℓ ∈ {n : ℕ | 0 < n ∧ ∃ f : F, f ≠ 0 ∧ w.ord (algebraMap F F f) = n} :=
    ⟨Nat.pos_of_ne_zero hℓ, y, hy0, hyord⟩
  have hlb : ∀ n ∈ {n : ℕ | 0 < n ∧ ∃ f : F, f ≠ 0 ∧ w.ord (algebraMap F F f) = n}, ℓ ≤ n := by
    rintro n ⟨hn, f, hf, hford⟩
    obtain ⟨x, hx⟩ := h.mem_range_pow f
    have hford' : (n : ℤ) = ℓ * w.ord x := by
      rw [← hford]
      show w.ord (φ f) = ℓ * w.ord x
      rw [hx, Place.ord_pow' w]
    have hxpos : 1 ≤ w.ord x := by
      by_cases hx1 : 1 ≤ w.ord x
      · exact hx1
      · exfalso
        have hle : (ℓ : ℤ) * w.ord x ≤ 0 :=
          mul_nonpos_iff.mpr (Or.inl ⟨by positivity, by omega⟩)
        omega
    have : (ℓ : ℤ) ≤ (n : ℤ) := by
      rw [hford']
      exact le_mul_of_one_le_right (by positivity) hxpos
    exact_mod_cast this
  exact le_antisymm (Nat.sInf_le hℓmem)
    (hlb _ (Nat.sInf_mem (Set.nonempty_of_mem hℓmem)))


-- created on 2026-10-23
