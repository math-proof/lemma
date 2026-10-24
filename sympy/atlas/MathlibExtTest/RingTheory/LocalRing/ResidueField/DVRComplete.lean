/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/LocalRing/ResidueField/DVRComplete.lean -/


import Lemma.Int.LocalRing.ResidueField.DVRComplete


variable {A B C : Type*}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
variable [Algebra A B] [Algebra A C]
variable [Module.Finite A B] [Module.Finite A C]
variable [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap A C)]

example [Algebra.Etale A B]
    [IsAdicComplete (IsLocalRing.maximalIdeal C) C] :
    Function.Bijective
      (DVRResidue.residueFieldMapAlgHom (A := A) (B := B) (C := C)) :=
  DVRResidue.residueFieldMapAlgHom_bijective_of_isAdicComplete

example [Algebra.Etale A B]
    [IsAdicComplete (IsLocalRing.maximalIdeal C) C]
    (φ : IsLocalRing.ResidueField B →ₐ[IsLocalRing.ResidueField A]
      IsLocalRing.ResidueField C) :
    ∃! f : B →ₐ[A] C, DVRResidue.residueFieldMapAlgHom f = φ :=
  by
    have hbij :=
      DVRResidue.residueFieldMapAlgHom_bijective_of_isAdicComplete
        (A := A) (B := B) (C := C)
    obtain ⟨f, hf⟩ := hbij.surjective φ
    refine ⟨f, hf, fun g hg => ?_⟩
    exact hbij.injective (hg.trans hf.symm)

example [Algebra.Etale A B] [Algebra.Etale A C]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    [IsAdicComplete (IsLocalRing.maximalIdeal C) C]
    (e : IsLocalRing.ResidueField B ≃ₐ[IsLocalRing.ResidueField A]
      IsLocalRing.ResidueField C) :
    ∃ e' : B ≃ₐ[A] C,
      DVRResidue.residueFieldMapAlgHom e'.toAlgHom = e.toAlgHom ∧
      DVRResidue.residueFieldMapAlgHom e'.symm.toAlgHom = e.symm.toAlgHom :=
  DVRResidue.exists_algEquiv_lift_residueField_of_isAdicComplete e

example [Algebra.Etale A B] [Algebra.Etale A C]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    [IsAdicComplete (IsLocalRing.maximalIdeal C) C]
    (e : IsLocalRing.ResidueField B ≃ₐ[IsLocalRing.ResidueField A]
      IsLocalRing.ResidueField C) :
    Nonempty (B ≃ₐ[A] C) := by
  obtain ⟨e', _, _⟩ :=
    DVRResidue.exists_algEquiv_lift_residueField_of_isAdicComplete e
  exact ⟨e'⟩
