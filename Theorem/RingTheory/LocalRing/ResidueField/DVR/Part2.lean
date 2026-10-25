/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/LocalRing/ResidueField/DVR.lean -/

import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.Filtration
import Def.RingTheory.LocalRing.ResidueField.DVR
variable {A B C D : Type*}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
variable [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
variable [Algebra A B] [Algebra A C] [Algebra A D]
variable [Module.Finite A B] [Module.Finite A C] [Module.Finite A D]
variable [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap A C)]
variable [IsLocalHom (algebraMap A D)]

/-!
# DVR residue-field functoriality: source-map stage for ATLAS N211

This file is a prerequisite stage for ATLAS NumberTheoryI item N211,
Theorem 10.13 (Section 10.2), at atlas-lean revision
`e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`. See the immutable
[N211 / Theorem 10.13 target, lines 1465-1483](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/targets.yaml#L1465-L1483):
equivalence between finite unramified extensions
of the fraction field of a complete DVR and finite separable extensions of its
residue field; on morphisms a field map is sent to reduction of a lifted
element, with the induced Hom-set bijection and isomorphism-class
correspondence.

This file works at the finite local DVR-ring level, one step below the fraction
fields and residue fields of the theorem. Source implementation:
[`v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean).

Source map from ATLAS N211 / Theorem 10.13 to this module's API:

* `DVRResidue.AlgHom.isLocalHom_of_isDiscreteValuationRing` supplies locality for
  an algebra homomorphism under this file's DVR, finite-module, and
  local-algebra hypotheses.
* `DVRResidue.residueFieldMapAlgHom` is the induced residue-field algebra map
  corresponding to the morphism part of Theorem 10.13; cf.
  [`residueFieldFunctorAlg`, lines 1001-1011](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L1001-L1011),
  where a homomorphism of finite
  local DVR extensions induces the residue-field algebra homomorphism by
  reducing a lift.
* `DVRResidue.residueFieldMapAlgHom_residue` states reduction of a lift.
* `DVRResidue.residueFieldMapAlgHom_id` and
  `DVRResidue.residueFieldMapAlgHom_comp` give the identity and composition laws
  needed for functoriality.
* Stage B, `DVRResidue.residueFieldMapAlgHom_injective`, formalizes only the
  faithfulness/injectivity direction of the Hom-set bijection in Theorem 10.13;
  cf. the
  [injectivity half of `residueFieldFunctor_full_faithfulness`, lines
  1013-1165](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L1013-L1165).
  This theorem does not require `Module.Finite A B`, so it genuinely
  generalizes the source's finite extension `B`. The target `C` remains finite
  over `A`, as required by the locality construction. The hypothesis
  `Algebra.FormallyUnramified A B` specializes the source's unramifiedness
  assumption, while Krull intersection in the target DVR converts equality
  after residue reduction into equality of algebra homomorphisms.

This stage proves the faithfulness part but not the full N211 target:
fullness/surjectivity on Hom sets, essential surjectivity, compatible lifting
of residue-field equivalences, and the category-equivalence/isomorphism-class
conclusion remain later stages, corresponding to the remainder of
`residueFieldFunctor_full_faithfulness` and to
[`residueFieldFunctor_isEquivalence`, lines 1320-1338](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L1320-L1338).
-/


namespace DVRResidue

omit [Module.Finite A B] in
@[simp]
theorem residueFieldMapAlgHom_residue (f : B →ₐ[A] C) (b : B) :
    residueFieldMapAlgHom f (IsLocalRing.residue B b) =
      IsLocalRing.residue C (f b) := by
  let := AlgHom.isLocalHom_of_isDiscreteValuationRing f
  simpa only [residueFieldMapAlgHom] using
    IsLocalRing.ResidueField.mapAlgHom'_residue f b

theorem residueFieldMapAlgHom_id :
    residueFieldMapAlgHom (AlgHom.id A B) = AlgHom.id _ _ := by
  ext x
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective x
  simp

omit [Module.Finite A B] in
theorem residueFieldMapAlgHom_comp (f : B →ₐ[A] C) (g : C →ₐ[A] D) :
    residueFieldMapAlgHom (g.comp f) =
      (residueFieldMapAlgHom g).comp (residueFieldMapAlgHom f) := by
  ext x
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective x
  simp

omit [Module.Finite A B] in
/-- Faithfulness of residue-field formation: for a formally unramified
extension, distinct `A`-algebra maps induce distinct residue-field maps. -/
theorem residueFieldMapAlgHom_injective
    [Algebra.FormallyUnramified A B] :
    Function.Injective
      (residueFieldMapAlgHom (A := A) (B := B) (C := C)) := by
  intro f g hfg
  have hne : IsLocalRing.maximalIdeal C ≠ ⊤ :=
    (IsLocalRing.maximalIdeal.isMaximal C).ne_top
  have hKrull : ⨅ n, (IsLocalRing.maximalIdeal C) ^ n = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal C) hne
  refine Algebra.FormallyUnramified.ext_of_iInf (IsLocalRing.maximalIdeal C)
    hKrull fun b => ?_
  have hres : IsLocalRing.residue C (f b) = IsLocalRing.residue C (g b) := by
    have h := DFunLike.congr_fun hfg (IsLocalRing.residue B b)
    simpa only [residueFieldMapAlgHom_residue] using h
  exact hres

end DVRResidue
