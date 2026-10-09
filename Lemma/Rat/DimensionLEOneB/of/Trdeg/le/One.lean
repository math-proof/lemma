import Mathlib
import sympy.Basic

open MvPolynomial

/--
[Ring_DimensionLEOne_of_finiteType_of_trdeg_le_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Ring_DimensionLEOne_of_finiteType_of_trdeg_le_one.lean)
-/
@[path]
private lemma main
  [Field k] [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
-- given
  (htr : Algebra.trdeg k B ≤ 1) :
-- imply
  Ring.DimensionLEOne B := by
-- proof
  classical
  obtain ⟨s, g, hg, hint⟩ := exists_integral_inj_algHom_of_fg k B

  have hs : s ≤ 1 := by
    have hind : AlgebraicIndependent k (fun i : Fin s => g (X i)) := by
      rw [algebraicIndependent_iff_injective_aeval]
      have : (aeval fun i : Fin s => g (X i) : MvPolynomial (Fin s) k →ₐ[k] B) = g := by
        ext i
        simp
      rw [this]; exact hg
    have h1 := hind.lift_cardinalMk_le_trdeg
    rw [Cardinal.mk_fin, Cardinal.lift_natCast] at h1
    have h2 : Cardinal.lift.{0} (Algebra.trdeg k B) ≤ Cardinal.lift.{0} (1 : Cardinal) := Cardinal.lift_le.2 htr
    rw [Cardinal.lift_one] at h2
    have h3 := h1.trans h2
    norm_cast at h3
  let : Algebra (MvPolynomial (Fin s) k) B := g.toRingHom.toAlgebra
  have : Algebra.IsIntegral (MvPolynomial (Fin s) k) B := ⟨hint⟩
  have : Ring.DimensionLEOne (MvPolynomial (Fin s) k) := by
    interval_cases s
    ·
      have : IsPrincipalIdealRing (MvPolynomial (Fin 0) k) :=
        IsPrincipalIdealRing.of_surjective (MvPolynomial.isEmptyRingEquiv k (Fin 0)).symm.toRingHom
          (MvPolynomial.isEmptyRingEquiv k (Fin 0)).symm.surjective
      infer_instance
    ·
      let e : MvPolynomial (Fin 1) k ≃ₐ[k] Polynomial k :=
        (MvPolynomial.finSuccEquiv k 0).trans (Polynomial.mapAlgEquiv (MvPolynomial.isEmptyAlgEquiv k (Fin 0)))
      have : IsPrincipalIdealRing (MvPolynomial (Fin 1) k) :=
        IsPrincipalIdealRing.of_surjective e.symm.toRingEquiv.toRingHom e.symm.surjective
      infer_instance
  exact Ring.DimensionLEOne.of_isIntegral (MvPolynomial (Fin s) k) B


-- created on 2026-10-05
