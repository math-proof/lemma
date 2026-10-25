import Mathlib
import Def.GaloisRep_Flat
import Def.FLTPrelim_Ramification

set_option autoImplicit false

noncomputable section

namespace GaloisRep

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

abbrev inertiaField (A : ValuationSubring ℚ̄) : IntermediateField ℚ ℚ̄ :=
  IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)

namespace InertiaRing

variable (A : ValuationSubring ℚ̄)

end InertiaRing

end GaloisRep

end

section PointTransportSection

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

open scoped TensorProduct
open WithConv

namespace GaloisRep.PointTransport

section LiftPt

variable {R S L H : Type*} [CommRing R] [CommRing S] [CommRing L] [CommRing H]
  [Algebra R S] [Algebra S L] [Algebra R L] [IsScalarTower R S L] [Algebra R H]

end LiftPt

section LiftPtConv

variable {R S L H : Type*} [CommRing R] [CommRing S] [CommRing L] [CommRing H]
  [Algebra R S] [Algebra S L] [Algebra R L] [IsScalarTower R S L] [Bialgebra R H]

end LiftPtConv

section EvGen

variable (K : Type*) (L : Type*) (B : Type*) [CommRing K] [CommRing L] [CommRing B] [Algebra K L] [Algebra K B]

end EvGen

section LiftPtMulEquiv

variable {R S L H : Type*} [CommRing R] [CommRing S] [CommRing L] [CommRing H]
  [Algebra R S] [Algebra S L] [Algebra R L] [IsScalarTower R S L] [Bialgebra R H]

end LiftPtMulEquiv

section Valuative

variable {R S L H : Type*} [CommRing R] [CommRing S] [Field L] [CommRing H]
  [Algebra R S] [Algebra S L] [Algebra R L] [IsScalarTower R S L] [Bialgebra R H]
  {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation L Γ₀)

end Valuative

end GaloisRep.PointTransport

noncomputable section

namespace GaloisRep.InertiaRing

section Dec

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable (A : ValuationSubring ℚ̄)

end Dec

section T1

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable (A : ValuationSubring ℚ̄)

end T1

end GaloisRep.InertiaRing

end

end PointTransportSection
