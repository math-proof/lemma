import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.LocalRing.ResidueField.DVRFull
open DVRResidue


/--
[exists_root_lift_of_adjoin_eq_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/LocalRing/ResidueField/DVRFull.lean)
-/
@[path]
private lemma exists_root_lift_of_adjoin_eq_top_eq
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [Algebra A B] [Algebra A C] [Module.Finite A B] [Module.Finite A C] [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap A C)] [Algebra.Etale A B] [HenselianLocalRing C]
  {beta : B}
  {f : IsLocalRing.ResidueField B →ₐ[IsLocalRing.ResidueField A] IsLocalRing.ResidueField C}
-- given
  (hbeta : Algebra.adjoin A {beta} = ⊤) :
-- imply
  exists gamma : C, Polynomial.aeval gamma (minpoly A beta) = 0 /\
    IsLocalRing.residue C gamma = f (IsLocalRing.residue B beta) := by
-- proof
  apply DVRResidue.exists_root_lift_of_adjoin_eq_top hbeta f

/--
[residueFieldMapAlgHom_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/LocalRing/ResidueField/DVRFull.lean)
-/
@[path]
private lemma residueFieldMapAlgHom_surjective_eq
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [Algebra A B] [Algebra A C] [Module.Finite A B] [Module.Finite A C] [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap A C)] [Algebra.Etale A B] [HenselianLocalRing C] :
-- imply
  Function.Surjective
    (residueFieldMapAlgHom (A := by
-- proof
  apply DVRResidue.residueFieldMapAlgHom_surjective


-- created on 2026-10-20
