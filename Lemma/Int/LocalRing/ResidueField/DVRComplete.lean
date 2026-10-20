import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.LocalRing.ResidueField.DVRComplete
open DVRResidue


/--
[residueFieldMapAlgHom_bijective_of_isAdicComplete](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/LocalRing/ResidueField/DVRComplete.lean)
-/
@[path]
private lemma residueFieldMapAlgHom_bijective_of_isAdicComplete_eq
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [Algebra A B] [Algebra A C] [Module.Finite A B] [Module.Finite A C] [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap A C)] [Algebra.Etale A B] [IsAdicComplete (IsLocalRing.maximalIdeal C) C] :
-- imply
  Function.Bijective
    (residueFieldMapAlgHom (A := by
-- proof
  apply DVRResidue.residueFieldMapAlgHom_bijective_of_isAdicComplete

/--
[exists_algEquiv_lift_residueField_of_isAdicComplete](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/LocalRing/ResidueField/DVRComplete.lean)
-/
@[path]
private lemma exists_algEquiv_lift_residueField_of_isAdicComplete_eq
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [Algebra A B] [Algebra A C] [Module.Finite A B] [Module.Finite A C] [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap A C)] [Algebra.Etale A B] [Algebra.Etale A C] [IsAdicComplete (IsLocalRing.maximalIdeal B) B] [IsAdicComplete (IsLocalRing.maximalIdeal C) C]
-- given
  (e : IsLocalRing.ResidueField B ≃ₐ[IsLocalRing.ResidueField A] IsLocalRing.ResidueField C) :
-- imply
  ∃ e' : B ≃ₐ[A] C,
    residueFieldMapAlgHom e'.toAlgHom = e.toAlgHom ∧
    residueFieldMapAlgHom e'.symm.toAlgHom = e.symm.toAlgHom := by
-- proof
  apply DVRResidue.exists_algEquiv_lift_residueField_of_isAdicComplete e


-- created on 2026-10-20
