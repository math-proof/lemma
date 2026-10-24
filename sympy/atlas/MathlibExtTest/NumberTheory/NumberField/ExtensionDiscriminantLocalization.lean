/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/ExtensionDiscriminantLocalization.lean -/


import Lemma.Nat.NumberField.ExtensionDiscriminantLocalization

-- Generic restatement applying `extensionDiscriminant_localization`.
example (A K : Type*) (L : Type*) (B : Type*) [CommRing A] [Field K]
    [CommRing B] [Field L] [Algebra A K] [Algebra B L] [Algebra A B]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    [FiniteDimensional K L] (S : Submonoid A)
    (SA : Type*) [CommRing SA] [Algebra A SA] [IsLocalization S SA]
    (SB : Type*) [CommRing SB] [Algebra B SB]
    [IsLocalization (Algebra.algebraMapSubmonoid B S) SB] [Algebra SA K]
    [Algebra SB L] [Algebra SA SB] [Algebra SA L] [IsScalarTower SA K L]
    [IsScalarTower SA SB L] [IsScalarTower A SA K] [IsScalarTower B SB L] :
    Submodule.span SA (extensionDiscriminant A K L B : Set K) =
      extensionDiscriminant SA K L SB :=
  extensionDiscriminant_localization A K L B S SA SB

namespace ConcreteLocalization

abbrev S : Submonoid ℤ := Submonoid.powers 2

abbrev SA := Localization S

theorem S_le_nonZeroDivisors : S ≤ nonZeroDivisors ℤ := by
  intro x hx
  rw [mem_nonZeroDivisors_iff_ne_zero]
  obtain ⟨n, rfl⟩ := hx
  exact pow_ne_zero n (by norm_num)

noncomputable local instance : Algebra SA (FractionRing ℤ) :=
  IsLocalization.localizationAlgebraOfSubmonoidLe SA (FractionRing ℤ) S
    (nonZeroDivisors ℤ) S_le_nonZeroDivisors

noncomputable abbrev q : SA :=
  IsLocalization.mk' (M := S) SA (1 : ℤ) (⟨2, Submonoid.mem_powers 2⟩ : S)

/- A concrete rank-one localization test.  The element `q` is the localization
  fraction `1 / 2`; its discriminant is `q ^ 2`.  The first conjunct puts this
  scaled discriminant in the scalar extension of the original discriminant,
  while the second puts the same element in the localized extension
  discriminant directly from its localized tuple. -/
example :
    ((algebraMap SA (FractionRing ℤ) q) ^ 2 ∈
        Submodule.span SA
          (extensionDiscriminant ℤ (FractionRing ℤ) (FractionRing ℤ) ℤ :
            Set (FractionRing ℤ))) ∧
      ((algebraMap SA (FractionRing ℤ) q) ^ 2 ∈
        extensionDiscriminant SA (FractionRing ℤ) (FractionRing ℤ) SA) := by
  have hone := discr_mem_extensionDiscriminant ℤ (FractionRing ℤ)
    (FractionRing ℤ) ℤ (b := fun _ => (1 : FractionRing ℤ))
      (fun _ => by simpa using algebraMap_mem_imageOfB ℤ (FractionRing ℤ) ℤ 1)
  rw [show Module.finrank (FractionRing ℤ) (FractionRing ℤ) = 1 by simp] at hone
  have hone' : (1 : FractionRing ℤ) ∈
      extensionDiscriminant ℤ (FractionRing ℤ) (FractionRing ℤ) ℤ := by
    simpa [Algebra.discr_def, Algebra.traceMatrix, Algebra.traceForm,
      Matrix.det_fin_one] using hone
  have hq : algebraMap SA (FractionRing ℤ) q ∈
      imageOfB SA (FractionRing ℤ) SA :=
    algebraMap_mem_imageOfB SA (FractionRing ℤ) SA q
  have hdisc := discr_mem_extensionDiscriminant SA (FractionRing ℤ)
    (FractionRing ℤ) SA (b := fun _ => algebraMap SA (FractionRing ℤ) q) (fun _ => hq)
  rw [show Module.finrank (FractionRing ℤ) (FractionRing ℤ) = 1 by simp] at hdisc
  have hmem : (algebraMap SA (FractionRing ℤ) q) ^ 2 ∈
      extensionDiscriminant SA (FractionRing ℤ) (FractionRing ℤ) SA := by
    simpa [Algebra.discr_def, Algebra.traceMatrix, Algebra.traceForm,
      Matrix.det_fin_one, Algebra.smul_def, pow_two] using hdisc
  constructor
  · have hspan : (1 : FractionRing ℤ) ∈ Submodule.span SA
        (extensionDiscriminant ℤ (FractionRing ℤ) (FractionRing ℤ) ℤ :
          Set (FractionRing ℤ)) :=
      Submodule.subset_span hone'
    have hscaled := Submodule.smul_mem
      (Submodule.span SA
        (extensionDiscriminant ℤ (FractionRing ℤ) (FractionRing ℤ) ℤ :
          Set (FractionRing ℤ))) (q ^ 2) hspan
    simpa [Algebra.smul_def] using hscaled
  · exact hmem

end ConcreteLocalization
