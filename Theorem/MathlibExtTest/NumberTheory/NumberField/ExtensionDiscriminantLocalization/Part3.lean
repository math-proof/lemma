/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/ExtensionDiscriminantLocalization.lean -/


import Lemma.Nat.NumberField.ExtensionDiscriminantLocalization
import Abbrev.MathlibExtTest.NumberTheory.NumberField.ExtensionDiscriminantLocalization.Part2


namespace ConcreteLocalization

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
