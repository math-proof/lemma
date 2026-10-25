/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/LocalRing/ResidueField/DVRFull.lean -/


import Lemma.Int.LocalRing.ResidueField.DVRFull
variable {A B C : Type*}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
variable [Algebra A B] [Algebra A C]
variable [Module.Finite A B] [Module.Finite A C]
variable [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap A C)]
variable [Algebra.Etale A B] [HenselianLocalRing C]


example :
    Function.Surjective
      (DVRResidue.residueFieldMapAlgHom (A := A) (B := B) (C := C)) :=
  DVRResidue.residueFieldMapAlgHom_surjective

example (f : IsLocalRing.ResidueField B →ₐ[IsLocalRing.ResidueField A]
    IsLocalRing.ResidueField C) :
    ∃ phi : B →ₐ[A] C, DVRResidue.residueFieldMapAlgHom phi = f :=
  DVRResidue.residueFieldMapAlgHom_surjective f

example (f : IsLocalRing.ResidueField B →ₐ[IsLocalRing.ResidueField A]
    IsLocalRing.ResidueField C) :
    ∃ phi : B →ₐ[A] C, ∀ b : B,
      IsLocalRing.residue C (phi b) = f (IsLocalRing.residue B b) := by
  obtain ⟨phi, hphi⟩ := DVRResidue.residueFieldMapAlgHom_surjective f
  refine ⟨phi, fun b => ?_⟩
  have h := AlgHom.congr_fun hphi (IsLocalRing.residue B b)
  simpa [DVRResidue.residueFieldMapAlgHom_residue] using h

