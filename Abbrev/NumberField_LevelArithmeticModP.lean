import Mathlib
import Abbrev.NumberField_SUnitsModule
import Instance.ExtEndgame_ProductionDatum
import Lemma.ClassGroup.GaloisAction
import Instance.Compat_Mathlib430

set_option autoImplicit false

noncomputable section

open CategoryTheory IsDedekindDomain
open scoped Pointwise NumberField nonZeroDivisors

namespace NumberField.LevelArith

section Bridge

variable (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L)

abbrev levelField : IntermediateField ↥K (AlgebraicClosure ℚ) := IntermediateField.extendScalars hKL

abbrev LevelGal : Type := ↥(levelField K L hKL) ≃ₐ[↥K] ↥(levelField K L hKL)

end Bridge

section ModP

variable {k : Type} [CommRing k] {G : Type} [Group G]

end ModP

section ClassGroups

variable (E F : Type) [Field E] [Field F] [NumberField F] [Algebra E F]

abbrev ringOfIntegersAut (σ : F ≃ₐ[E] F) : 𝓞 F ≃+* 𝓞 F := NumberField.RingOfIntegers.mapRingEquiv (σ : F ≃+* F)

abbrev classGroupRep : Rep ℤ (F ≃ₐ[E] F) := Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (ClassGroup (𝓞 F))

end ClassGroups

section Quartet

variable (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L) [Normal ↥K ↥(levelField K L hKL)]
  [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L] (S : Finset Nat.Primes) (p : ℕ)

end Quartet

section Places

variable (K L : IntermediateField ℚ (AlgebraicClosure ℚ))

abbrev IsNormalLevel : Prop := ∀ g ∈ K.fixingSubgroup, ∀ s ∈ L.fixingSubgroup, g * s * g⁻¹ ∈ L.fixingSubgroup

abbrev placesAbove (S : Finset Nat.Primes) (v : ExtCitation.extArithIndex S) : Type :=
  MulAction.orbitRel.Quotient ↥L.fixingSubgroup ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (ExtCitation.extArithLoc S v).range)

end Places

end NumberField.LevelArith

end
