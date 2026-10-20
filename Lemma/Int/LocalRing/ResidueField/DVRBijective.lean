import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.LocalRing.ResidueField.DVRBijective
open DVRResidue


/--
[residueFieldMapAlgHom_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/LocalRing/ResidueField/DVRBijective.lean)
-/
@[path]
private lemma residueFieldMapAlgHom_bijective_eq
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [Algebra A B] [Algebra A C] [Module.Finite A B] [Module.Finite A C] [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap A C)] [Algebra.Etale A B] [HenselianLocalRing C] :
-- imply
  Function.Bijective
    (residueFieldMapAlgHom (A := by
-- proof
  apply DVRResidue.residueFieldMapAlgHom_bijective

/--
[exists_algEquiv_lift_residueField](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/LocalRing/ResidueField/DVRBijective.lean)
-/
@[path]
private lemma exists_algEquiv_lift_residueField_eq
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [Algebra A B] [Algebra A C] [Module.Finite A B] [Module.Finite A C] [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap A C)] [Algebra.Etale A B] [Algebra.Etale A C] [HenselianLocalRing B] [HenselianLocalRing C]
-- given
  (e : IsLocalRing.ResidueField B ≃ₐ[IsLocalRing.ResidueField A] IsLocalRing.ResidueField C) :
-- imply
  ∃ e' : B ≃ₐ[A] C,
    residueFieldMapAlgHom e'.toAlgHom = e.toAlgHom ∧
    residueFieldMapAlgHom e'.symm.toAlgHom = e.symm.toAlgHom := by
-- proof
  apply DVRResidue.exists_algEquiv_lift_residueField e


-- created on 2026-10-20
