import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.RingTheory.LocalRing.ResidueField.DVR.Part2
open DVRResidue
open AlgHom


/--
[isLocalHom_of_isDiscreteValuationRing](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/LocalRing/ResidueField/DVR.lean)
-/
@[path]
private lemma isLocalHom_of_isDiscreteValuationRing_eq
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] [Algebra A B] [Algebra A C] [Algebra A D] [Module.Finite A B] [Module.Finite A C] [Module.Finite A D] [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap A C)] [IsLocalHom (algebraMap A D)]
  {f : B →ₐ[A] C} :
-- imply
  IsLocalHom f := by
-- proof
  apply DVRResidue.AlgHom.isLocalHom_of_isDiscreteValuationRing f

/--
[residueFieldMapAlgHom_residue](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/LocalRing/ResidueField/DVR.lean)
-/
@[path]
private lemma residueFieldMapAlgHom_residue_eq
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] [Algebra A B] [Algebra A C] [Algebra A D] [Module.Finite A B] [Module.Finite A C] [Module.Finite A D] [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap A C)] [IsLocalHom (algebraMap A D)]
  {f : B →ₐ[A] C}
  {b : B} :
-- imply
  residueFieldMapAlgHom f (IsLocalRing.residue B b) =
    IsLocalRing.residue C (f b) := by
-- proof
  apply DVRResidue.residueFieldMapAlgHom_residue f b

/--
[residueFieldMapAlgHom_id](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/LocalRing/ResidueField/DVR.lean)
-/
@[path]
private lemma residueFieldMapAlgHom_id_eq
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] [Algebra A B] [Algebra A C] [Algebra A D] [Module.Finite A B] [Module.Finite A C] [Module.Finite A D] [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap A C)] [IsLocalHom (algebraMap A D)] :
-- imply
  residueFieldMapAlgHom (AlgHom.id A B) = AlgHom.id _ _ := by
-- proof
  apply DVRResidue.residueFieldMapAlgHom_id

/--
[residueFieldMapAlgHom_comp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/LocalRing/ResidueField/DVR.lean)
-/
@[path]
private lemma residueFieldMapAlgHom_comp_eq
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] [Algebra A B] [Algebra A C] [Algebra A D] [Module.Finite A B] [Module.Finite A C] [Module.Finite A D] [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap A C)] [IsLocalHom (algebraMap A D)]
  {f : B →ₐ[A] C}
  {g : C →ₐ[A] D} :
-- imply
  residueFieldMapAlgHom (g.comp f) =
    (residueFieldMapAlgHom g).comp (residueFieldMapAlgHom f) := by
-- proof
  apply DVRResidue.residueFieldMapAlgHom_comp f g

/--
[residueFieldMapAlgHom_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/LocalRing/ResidueField/DVR.lean)
-/
@[path]
private lemma residueFieldMapAlgHom_injective_eq
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] [Algebra A B] [Algebra A C] [Algebra A D] [Module.Finite A B] [Module.Finite A C] [Module.Finite A D] [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap A C)] [IsLocalHom (algebraMap A D)] [Algebra.FormallyUnramified A B] :
-- imply
  Function.Injective
    (residueFieldMapAlgHom (A := A) (B := B) (C := C)) := by
-- proof
  apply DVRResidue.residueFieldMapAlgHom_injective


-- created on 2026-10-20
-- updated on 2026-10-26
