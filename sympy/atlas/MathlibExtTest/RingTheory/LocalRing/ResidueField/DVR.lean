/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/LocalRing/ResidueField/DVR.lean -/


import sympy.atlas.RingTheory.LocalRing.ResidueField.DVR
import Lemma.AlgHom.LocalRing.ResidueField.DVR


variable {A B C D : Type*}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
variable [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
variable [Algebra A B] [Algebra A C] [Algebra A D]
variable [Module.Finite A B] [Module.Finite A C] [Module.Finite A D]
variable [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap A C)]
variable [IsLocalHom (algebraMap A D)]

example (f : B →ₐ[A] C) : IsLocalHom f :=
  DVRResidue.AlgHom.isLocalHom_of_isDiscreteValuationRing f

example (f : B →ₐ[A] C) (b : B) :
    DVRResidue.residueFieldMapAlgHom f (IsLocalRing.residue B b) =
      IsLocalRing.residue C (f b) := by
  simp

example :
    DVRResidue.residueFieldMapAlgHom (AlgHom.id A B) = AlgHom.id _ _ :=
  DVRResidue.residueFieldMapAlgHom_id

example (f : B →ₐ[A] C) (g : C →ₐ[A] D) :
    DVRResidue.residueFieldMapAlgHom (g.comp f) =
      (DVRResidue.residueFieldMapAlgHom g).comp
        (DVRResidue.residueFieldMapAlgHom f) :=
  DVRResidue.residueFieldMapAlgHom_comp f g

example [Algebra.FormallyUnramified A B] (f g : B →ₐ[A] C)
    (h : DVRResidue.residueFieldMapAlgHom f =
      DVRResidue.residueFieldMapAlgHom g) : f = g :=
  DVRResidue.residueFieldMapAlgHom_injective h
