import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_AlgebraicCurve_FrobeniusEndo
open AlgebraicCurve


namespace Definitions
end Definitions

/--
[AlgebraicCurve_IsFrobeniusEndo_ramificationIndexAlong_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_IsFrobeniusEndo_ramificationIndexAlong_eq.lean)
-/
@[path]
private lemma main
  [Field K] [Field F] [Algebra K F]
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
    rw [hy]
    have hpow : w.ord ((π : F) ^ ℓ) = (ℓ : ℤ) * w.ord (π : F) := by
      have := w.ord_zpow (π : F) (ℓ : ℤ)
      rwa [zpow_natCast] at this
    rw [hpow, w.ord_coe_irreducible hπ, mul_one]
  have hℓmem : ℓ ∈ {n : ℕ | 0 < n ∧ ∃ f : F, f ≠ 0 ∧ w.ord (algebraMap F F f) = n} :=
    ⟨Nat.pos_of_ne_zero hℓ, y, hy0, hyord⟩
  refine le_antisymm (Nat.sInf_le hℓmem) ?_
  obtain ⟨hn, f, hf, hford⟩ := Nat.sInf_mem (Set.nonempty_of_mem hℓmem)
  obtain ⟨x, hx⟩ := h.mem_range_pow f
  have hford' : w.ord (algebraMap F F f) = ℓ * w.ord x := by
    show w.ord (φ f) = ℓ * w.ord x
    rw [hx]
    have hpow : w.ord (x ^ ℓ) = (ℓ : ℤ) * w.ord x := by
      have := w.ord_zpow x (ℓ : ℤ)
      rwa [zpow_natCast] at this
    rw [hpow]
  have hxpos : 1 ≤ w.ord x := by
    if hx1 : 1 ≤ w.ord x then
      exact hx1
    else
      exfalso
      have hle : (ℓ : ℤ) * w.ord x ≤ 0 :=
        mul_nonpos_iff.mpr (Or.inl ⟨by positivity, by omega⟩)
      omega
  have hle : (ℓ : ℤ) ≤ w.ord (algebraMap F F f) := by
    rw [hford']
    exact le_mul_of_one_le_right (by positivity) hxpos
  exact_mod_cast (hford ▸ hle)


-- created on 2026-10-24
