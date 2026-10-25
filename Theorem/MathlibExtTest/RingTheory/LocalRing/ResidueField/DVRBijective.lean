/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/LocalRing/ResidueField/DVRBijective.lean -/


import Lemma.Int.LocalRing.ResidueField.DVRBijective
variable {A B C : Type*}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
variable [Algebra A B] [Algebra A C]
variable [Module.Finite A B] [Module.Finite A C]
variable [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap A C)]
variable [Algebra.Etale A B] [HenselianLocalRing C]


example :
    Function.Bijective
      (DVRResidue.residueFieldMapAlgHom (A := A) (B := B) (C := C)) :=
  DVRResidue.residueFieldMapAlgHom_bijective

example :
    Function.Injective
      (DVRResidue.residueFieldMapAlgHom (A := A) (B := B) (C := C)) :=
  DVRResidue.residueFieldMapAlgHom_bijective.injective

example (f : IsLocalRing.ResidueField B →ₐ[IsLocalRing.ResidueField A]
    IsLocalRing.ResidueField C) :
    ∃! phi : B →ₐ[A] C, DVRResidue.residueFieldMapAlgHom phi = f := by
  obtain ⟨phi, hphi⟩ := DVRResidue.residueFieldMapAlgHom_surjective f
  refine ⟨phi, hphi, fun psi hpsi => ?_⟩
  apply DVRResidue.residueFieldMapAlgHom_injective
  rw [hpsi, hphi]

section Lift

variable [Algebra.Etale A C] [HenselianLocalRing B]

example (e : IsLocalRing.ResidueField B ≃ₐ[IsLocalRing.ResidueField A]
    IsLocalRing.ResidueField C) :
    ∃ e' : B ≃ₐ[A] C,
      DVRResidue.residueFieldMapAlgHom e'.toAlgHom = e.toAlgHom ∧
        DVRResidue.residueFieldMapAlgHom e'.symm.toAlgHom =
          e.symm.toAlgHom :=
  DVRResidue.exists_algEquiv_lift_residueField e

example (e : IsLocalRing.ResidueField B ≃ₐ[IsLocalRing.ResidueField A]
    IsLocalRing.ResidueField C) : Nonempty (B ≃ₐ[A] C) := by
  obtain ⟨e', _, _⟩ := DVRResidue.exists_algEquiv_lift_residueField e
  exact ⟨e'⟩

example (e : IsLocalRing.ResidueField B ≃ₐ[IsLocalRing.ResidueField A]
    IsLocalRing.ResidueField C) :
    ∃ e' : B ≃ₐ[A] C,
      DVRResidue.residueFieldMapAlgHom e'.toAlgHom = e.toAlgHom := by
  obtain ⟨e', hf, _⟩ := DVRResidue.exists_algEquiv_lift_residueField e
  exact ⟨e', hf⟩

end Lift
