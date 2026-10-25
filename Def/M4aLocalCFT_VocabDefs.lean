import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

open IsLocalRing ValuationSubring

namespace M4aLocalCFT

section Carrier

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (A : ValuationSubring L) [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal (A : Type _)) A]
variable [Finite (IsLocalRing.ResidueField A)]
variable [Finite (A.decompositionSubgroup K)] [IsCyclic (A.decompositionSubgroup K)]

noncomputable def unitsAct (s : A.decompositionSubgroup K) : Aˣ →* Aˣ :=
  Units.map (MulSemiringAction.toRingAut (A.decompositionSubgroup K) A s).toRingHom.toMonoidHom

noncomputable def unitsNorm : Aˣ →* Aˣ :=
  letI := Fintype.ofFinite (A.decompositionSubgroup K)
  ∏ s : A.decompositionSubgroup K, unitsAct A s

noncomputable def unitsDerive (g : A.decompositionSubgroup K) : Aˣ →* Aˣ :=
  (unitsAct A g) / (MonoidHom.id Aˣ)

end Carrier

section FieldUnits

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (A : ValuationSubring L) [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal (A : Type _)) A]
variable [Finite (IsLocalRing.ResidueField A)]
variable [Finite (A.decompositionSubgroup K)] [IsCyclic (A.decompositionSubgroup K)]

noncomputable def fieldUnitsAct (s : A.decompositionSubgroup K) : Lˣ →* Lˣ :=
  Units.map (s : L ≃ₐ[K] L).toAlgHom.toRingHom.toMonoidHom

noncomputable def fieldUnitsNorm : Lˣ →* Lˣ :=
  letI := Fintype.ofFinite (A.decompositionSubgroup K)
  ∏ s : A.decompositionSubgroup K, fieldUnitsAct A s

noncomputable def fieldUnitsDerive (g : A.decompositionSubgroup K) : Lˣ →* Lˣ :=
  (fieldUnitsAct A g) / (MonoidHom.id Lˣ)

end FieldUnits

end M4aLocalCFT
