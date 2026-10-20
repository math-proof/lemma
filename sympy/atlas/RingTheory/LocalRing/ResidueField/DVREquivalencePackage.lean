/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/LocalRing/ResidueField/DVREquivalencePackage.lean -/

import sympy.atlas.RingTheory.DiscreteValuationRing.Monogenic
import sympy.atlas.RingTheory.LocalRing.ResidueField.AdjoinRootLift
import sympy.atlas.RingTheory.LocalRing.ResidueField.DVRComplete
/-!
# Partial residue-field equivalence package for finite DVR extensions

## ATLAS source correspondence

This packages three support results toward ATLAS NumberTheoryI N211, Theorem
10.13. It is deliberately not the full source theorem. At atlas-lean commit
`e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`, the theorem is indexed in
[`v1/Atlas/NumberTheoryI/targets.yaml`, lines 1466--1483](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/targets.yaml#L1466-L1483):
reduction from finite unramified extensions of a complete DVR to finite
separable residue extensions is essentially surjective and induces bijections
on Hom sets, hence a bijection on isomorphism classes. The primary formal
package is `residueFieldFunctor_isEquivalence` in
[`v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean`, lines 1320--1338](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L1320-L1338).

`residueField_partial_equivalence_package_of_isAdicComplete` maps its conjuncts
as follows:

1. `Function.Bijective (residueFieldMapAlgHom ...)` is source lines 1323 and
   1336, the full-faithfulness/Hom-set bijection for `B₁` and `B₂`.
2. The quantified existence of `B` realizing every finite separable residue
   extension `L` uses the construction at
   [lines 1174--1203](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L1174-L1203).
   Unlike source lines 1325--1332, this conjunct does not return
   `Algebra.Etale A B` or `IsUnramifiedDVRExtension`; therefore it is only a
   finite-local-DVR realization and not categorical essential surjectivity.
3. The lift of a residue-field `AlgEquiv` to `B₁ ≃ₐ[A] B₂` is source lines
   1334--1337 and the injectivity construction at
   [lines 1220--1303](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L1220-L1303).
   This API
   additionally exposes the forward and inverse reduction equations that the
   source proof establishes.

The section assumptions match the source finite local DVR extensions. The
separability instances and `hfin₁`, `hfin₂` are exactly the two fields of the
source `IsUnramifiedDVRExtension` predicate; the preceding N211 stage converts
them to the `Algebra.Etale` instances needed by the component APIs. Adic
completeness of `B₁` and `B₂` supplies the lifting/full-faithfulness results.

This is a proposition-level partial support package rather than the source
equivalence or a constructed `CategoryTheory.Equivalence`. In particular,
clause 2 deliberately lacks an `Algebra.Etale A B` field, so callers must not
treat its object as belonging to the source category of unramified extensions.

## Main results

* `DVRResidue.residueField_partial_equivalence_package_of_isAdicComplete`: a
  partial package combining Hom-set bijectivity, finite-local-DVR realization,
  and lifting of residue-field equivalences.
-/

universe u v

namespace DVRResidue

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {B₁ B₂ : Type u}
variable [CommRing B₁] [IsDomain B₁] [IsDiscreteValuationRing B₁]
variable [CommRing B₂] [IsDomain B₂] [IsDiscreteValuationRing B₂]
variable [Algebra A B₁] [Algebra A B₂]
variable [Module.Finite A B₁] [Module.Finite A B₂]
variable [IsLocalHom (algebraMap A B₁)] [IsLocalHom (algebraMap A B₂)]
variable [IsAdicComplete (IsLocalRing.maximalIdeal B₁) B₁]
variable [IsAdicComplete (IsLocalRing.maximalIdeal B₂) B₂]
variable [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B₁)]
variable [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B₂)]

/-- Partial support package: Hom-set bijectivity, finite-local-DVR realization
  without an unramifiedness claim, and lifting of residue-field equivalences.
  The finrank equalities together with the separable residue extensions supply
  the étale hypotheses only for the fixed objects `B₁` and `B₂`. -/
theorem residueField_partial_equivalence_package_of_isAdicComplete
    (hfin₁ : Module.finrank A B₁ =
      Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B₁))
    (hfin₂ : Module.finrank A B₂ =
      Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B₂)) :
    Function.Bijective (residueFieldMapAlgHom (A := A) (B := B₁) (C := B₂)) ∧
    (∀ (L : Type v) [Field L] [Algebra (IsLocalRing.ResidueField A) L]
      [FiniteDimensional (IsLocalRing.ResidueField A) L]
      [Algebra.IsSeparable (IsLocalRing.ResidueField A) L],
      ∃ (B : Type u) (_ : CommRing B) (_ : IsDomain B) (_ : Algebra A B)
        (_ : Module.Finite A B) (_ : IsDiscreteValuationRing B)
        (_ : IsLocalHom (algebraMap A B)),
        Nonempty (IsLocalRing.ResidueField B ≃ₐ[IsLocalRing.ResidueField A] L)) ∧
    (∀ (e : IsLocalRing.ResidueField B₁ ≃ₐ[IsLocalRing.ResidueField A]
        IsLocalRing.ResidueField B₂),
      ∃ e' : B₁ ≃ₐ[A] B₂,
        residueFieldMapAlgHom e'.toAlgHom = e.toAlgHom ∧
        residueFieldMapAlgHom e'.symm.toAlgHom = e.symm.toAlgHom) := by
  let _ : Algebra.Etale A B₁ :=
    IsDiscreteValuationRing.etale_of_isSeparable_residueField_of_finrank_eq hfin₁
  let _ : Algebra.Etale A B₂ :=
    IsDiscreteValuationRing.etale_of_isSeparable_residueField_of_finrank_eq hfin₂
  refine ⟨residueFieldMapAlgHom_bijective_of_isAdicComplete, ?_, ?_⟩
  · intro L _ _ _ _
    exact exists_finite_dvr_extension_residueField_algEquiv L
  · intro e
    exact exists_algEquiv_lift_residueField_of_isAdicComplete e

end DVRResidue
