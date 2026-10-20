import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.LocalRing.ResidueField.DVREquivalencePackage
open DVRResidue


/--
[residueField_partial_equivalence_package_of_isAdicComplete](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/LocalRing/ResidueField/DVREquivalencePackage.lean)
-/
@[path]
private lemma residueField_partial_equivalence_package_of_isAdicComplete_eq
  {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {B₁ B₂ : Type u} [CommRing B₁] [IsDomain B₁] [IsDiscreteValuationRing B₁] [CommRing B₂] [IsDomain B₂] [IsDiscreteValuationRing B₂] [Algebra A B₁] [Algebra A B₂] [Module.Finite A B₁] [Module.Finite A B₂] [IsLocalHom (algebraMap A B₁)] [IsLocalHom (algebraMap A B₂)] [IsAdicComplete (IsLocalRing.maximalIdeal B₁) B₁] [IsAdicComplete (IsLocalRing.maximalIdeal B₂) B₂] [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B₁)] [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B₂)]
-- given
  (hfin₁ : Module.finrank A B₁ = Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B₁))
  (hfin₂ : Module.finrank A B₂ = Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B₂)) :
-- imply
  Function.Bijective (residueFieldMapAlgHom (A := by
-- proof
  apply DVRResidue.residueField_partial_equivalence_package_of_isAdicComplete hfin₁ hfin₂


-- created on 2026-10-20
