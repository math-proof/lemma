import Mathlib
import sympy.Basic

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate

/--
[WeierstrassCurve_Affine_CoordinateRing_isUnit_iff_eq_algebraMap](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_CoordinateRing_isUnit_iff_eq_algebraMap.lean)
-/
@[main]
private lemma main
  [Field F]
  {W : WeierstrassCurve F}
  {f : W.toAffine.CoordinateRing} :
-- imply
  IsUnit f ↔ ∃ c : F, c ≠ 0 ∧ f = algebraMap F W.toAffine.CoordinateRing c := by
-- proof
  constructor
  · intro hf
    obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq f
    have hnu : IsUnit (Algebra.norm F[X] (p • (1 : W.toAffine.CoordinateRing) +
        q • CoordinateRing.mk W.toAffine Y)) := hf.map _
    have hdeg := Polynomial.degree_eq_zero_of_isUnit hnu
    rw [CoordinateRing.degree_norm_smul_basis] at hdeg

    have hq : q = 0 := by
      by_contra hq
      have h3 : (2 • q.degree + 3 : WithBot ℕ) = ((2 * q.natDegree + 3 : ℕ) : WithBot ℕ) := by
        rw [Polynomial.degree_eq_natDegree hq]
        norm_cast
      have hle : ((2 * q.natDegree + 3 : ℕ) : WithBot ℕ) ≤ (0 : WithBot ℕ) := by
        rw [← h3, ← hdeg]
        exact le_max_right _ _
      have hle' : 2 * q.natDegree + 3 ≤ 0 := by exact_mod_cast hle
      omega
    subst hq
    rw [zero_smul, add_zero] at hnu ⊢

    have hnp : Algebra.norm F[X] (p • (1 : W.toAffine.CoordinateRing)) = p ^ 2 := by
      have := CoordinateRing.norm_smul_basis (W' := W.toAffine) p 0
      rw [zero_smul, add_zero] at this
      rw [this]
      ring
    rw [hnp, isUnit_pow_iff two_ne_zero, Polynomial.isUnit_iff] at hnu
    obtain ⟨c, hc, rfl⟩ := hnu
    refine ⟨c, hc.ne_zero, ?_⟩
    rw [CoordinateRing.smul, mul_one]
    rfl
  · rintro ⟨c, hc, rfl⟩
    exact (IsUnit.mk0 c hc).map _


-- created on 2026-10-05
