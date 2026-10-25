/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/FieldTheory/Galois/Abelian.lean -/


import Mathlib.NumberTheory.Cyclotomic.Basic
import Theorem.FieldTheory.Galois.Abelian
import Lemma.Rat.Galois.Abelian
/-!
# Tests for the abelian Galois modular-lattice constructor

Compile-time checks for `IsAbelianGalois.isModularLattice_intermediateField`: a
generic direct-constructor example, a local modular-law example using every
structural hypothesis, and a source-shaped cyclotomic-field example matching the
ATLAS `cyclotomicIntermediateFieldModular` use case
(`Atlas/NumberTheoryI/code/AnalyticClassNumber.lean`, lines 1640--1651).
-/


namespace MathlibExtTest.FieldTheory.Galois.Abelian

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [IsAbelianGalois K L]

-- Generic direct-constructor example.
example : IsModularLattice (IntermediateField K L) :=
  IsAbelianGalois.isModularLattice_intermediateField

-- Local modular-law example; every structural hypothesis above
-- (`Field K`, `Field L`, `Algebra K L`, `FiniteDimensional K L`,
-- `IsAbelianGalois K L`) is consumed by the constructor.
example (x y z : IntermediateField K L) (hxz : x ≤ z) :
    (x ⊔ y) ⊓ z ≤ x ⊔ y ⊓ z := by
  let _ : IsModularLattice (IntermediateField K L) :=
    IsAbelianGalois.isModularLattice_intermediateField
  exact IsModularLattice.sup_inf_le_assoc_of_le y hxz

-- Source-shaped cyclotomic-field example: as in the ATLAS proof, the cyclotomic
-- extension supplies the abelian Galois hypothesis, then the constructor applies.
example (m : ℕ) [NeZero m] :
    IsModularLattice (IntermediateField ℚ (CyclotomicField m ℚ)) := by
  let _ : NeZero ((m : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne m)⟩
  let _ : IsCyclotomicExtension {m} ℚ (CyclotomicField m ℚ) :=
    CyclotomicField.isCyclotomicExtension m ℚ
  let _ : IsAbelianGalois ℚ (CyclotomicField m ℚ) :=
    IsCyclotomicExtension.isAbelianGalois {m} ℚ (CyclotomicField m ℚ)
  exact IsAbelianGalois.isModularLattice_intermediateField

end MathlibExtTest.FieldTheory.Galois.Abelian
