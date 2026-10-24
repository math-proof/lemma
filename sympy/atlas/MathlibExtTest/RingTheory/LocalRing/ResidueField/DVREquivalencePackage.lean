/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/LocalRing/ResidueField/DVREquivalencePackage.lean -/


import Lemma.Int.LocalRing.ResidueField.DVREquivalencePackage


universe u v

open DVRResidue

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {B₁ B₂ : Type u}
variable [CommRing B₁] [IsDomain B₁] [IsDiscreteValuationRing B₁]
variable [CommRing B₂] [IsDomain B₂] [IsDiscreteValuationRing B₂]
variable [Algebra A B₁] [Algebra A B₂]
variable [Module.Finite A B₁] [Module.Finite A B₂]
variable [IsLocalHom (algebraMap A B₁)] [IsLocalHom (algebraMap A B₂)]
variable [IsAdicComplete (IsLocalRing.maximalIdeal B₁) B₁]
variable [IsAdicComplete (IsLocalRing.maximalIdeal B₂) B₂]
variable [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B₁)]
variable [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B₂)]

example
    (hfin₁ : Module.finrank A B₁ =
      Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B₁))
    (hfin₂ : Module.finrank A B₂ =
      Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B₂)) :
    Function.Bijective (DVRResidue.residueFieldMapAlgHom (A := A) (B := B₁) (C := B₂)) ∧
    (∀ (L : Type v) [Field L] [Algebra (IsLocalRing.ResidueField A) L]
      [FiniteDimensional (IsLocalRing.ResidueField A) L]
      [Algebra.IsSeparable (IsLocalRing.ResidueField A) L],
      ∃ (B : Type u) (_ : CommRing B) (_ : IsDomain B) (_ : Algebra A B)
        (_ : Module.Finite A B) (_ : IsDiscreteValuationRing B)
        (_ : IsLocalHom (algebraMap A B)),
        Nonempty (IsLocalRing.ResidueField B ≃ₐ[IsLocalRing.ResidueField A] L)) ∧
    (∀ (e : IsLocalRing.ResidueField B₁ ≃ₐ[IsLocalRing.ResidueField A]
        IsLocalRing.ResidueField B₂),
      ∃ e' : B₁ ≃ₐ[A] B₂,
        DVRResidue.residueFieldMapAlgHom e'.toAlgHom = e.toAlgHom ∧
        DVRResidue.residueFieldMapAlgHom e'.symm.toAlgHom = e.symm.toAlgHom) :=
  DVRResidue.residueField_partial_equivalence_package_of_isAdicComplete hfin₁ hfin₂

example
    (hfin₁ : Module.finrank A B₁ =
      Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B₁))
    (hfin₂ : Module.finrank A B₂ =
      Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B₂))
    (L : Type v) [Field L] [Algebra (IsLocalRing.ResidueField A) L]
    [FiniteDimensional (IsLocalRing.ResidueField A) L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) L] :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsDomain B) (_ : Algebra A B)
      (_ : Module.Finite A B) (_ : IsDiscreteValuationRing B)
      (_ : IsLocalHom (algebraMap A B))
      (e : IsLocalRing.ResidueField B ≃ₐ[IsLocalRing.ResidueField A] L),
      Function.Bijective (e : IsLocalRing.ResidueField B →
        L) := by
  have h := DVRResidue.residueField_partial_equivalence_package_of_isAdicComplete
    (A := A) (B₁ := B₁) (B₂ := B₂) hfin₁ hfin₂
  obtain ⟨-, hobj, -⟩ := h
  obtain ⟨B, hB₁, hB₂, hB₃, hB₄, hB₅, hB₆, hne⟩ := hobj L
  obtain ⟨e⟩ := hne
  exact ⟨B, hB₁, hB₂, hB₃, hB₄, hB₅, hB₆, e, e.bijective⟩
