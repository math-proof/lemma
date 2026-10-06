import Mathlib
import sympy.Basic

open CategoryTheory AlgebraicGeometry

/--
[AlgebraicGeometry_IsClosedImmersion_exists_ringEquiv_residueField_functionField_of_isIntegral](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_IsClosedImmersion_exists_ringEquiv_residueField_functionField_of_isIntegral.lean)
-/
@[main]
private lemma main
  {C Y : Scheme.{u}} [IsIntegral C]
  {i : C ⟶ Y} [IsClosedImmersion i] :
-- imply
  ∃ θ : Y.residueField (i.base (genericPoint C)) ≃+* C.functionField,
      ∀ s : Y.presheaf.stalk (i.base (genericPoint C)),
        θ ((Y.residue (i.base (genericPoint C))).hom s) = (i.stalkMap (genericPoint C)).hom s := by
-- proof
  set ξ := genericPoint C with hξ
  let φ : Y.presheaf.stalk (i.base ξ) →+* C.functionField := (i.stalkMap ξ).hom
  have hsurj : Function.Surjective φ := i.stalkMap_surjective ξ
  haveI : IsLocalHom φ := i.toLRSHom.prop ξ

  have hker : RingHom.ker φ = IsLocalRing.maximalIdeal _ := by
    ext s
    rw [RingHom.mem_ker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    constructor
    · intro h hu
      exact not_isUnit_zero (h ▸ hu.map φ)
    · intro h
      by_contra hne
      exact h (isUnit_of_map_unit φ s (isUnit_iff_ne_zero.mpr hne))
  refine ⟨(Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj), fun s => rfl⟩


-- created on 2026-10-05
