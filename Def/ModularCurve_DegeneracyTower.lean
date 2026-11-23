module

public import Def.ModularCurve_HeckeOperator

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open AlgebraicCurve


section TowerMaps

variable (L : Type*) [Field L] [Algebra ℚ L] {N M : ℕ} [NeZero N] [NeZero M]

def towerInclBar (h : N ∣ M) :
    laurentBaseChange L (modularFunctionFieldFull N) →ₐ[L]
      laurentBaseChange L (modularFunctionFieldFull M) :=
  IntermediateField.inclusion (laurentBaseChange_mono'' L (full_degeneracy_le h))

variable (N) in

def towerSubstBar (ℓ : ℕ) [NeZero ℓ] (h : N * ℓ ∣ M) :
    laurentBaseChange L (modularFunctionFieldFull N) →ₐ[L]
      laurentBaseChange L (modularFunctionFieldFull M) :=
  (towerInclBar L h).comp (heckeBetaBar L N ℓ)

end TowerMaps

section Composites

variable (L : Type*) [Field L] [Algebra ℚ L] {N M : ℕ} [NeZero N] [NeZero M] (ℓ ℓ' : ℕ)
  [NeZero ℓ] [NeZero ℓ']

end Composites

section Exchange

variable (L : Type*) [Field L] [Algebra ℚ L] (N ℓ ℓ' M : ℕ) [NeZero N] [NeZero ℓ] [NeZero ℓ']
  [NeZero M]

omit [NeZero N] [NeZero ℓ] [NeZero ℓ'] [NeZero M] in

def HeckeExchangeAt (hM : M = N * ℓ * ℓ') : Prop :=
  ∀ [HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull (N * ℓ)))]
    [HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull M))]
    (hβ : (heckeBetaBar L N ℓ).toRingHom.IsIntegral)
    (hα' : (heckeAlphaBar L N ℓ').toRingHom.IsIntegral)
    (hu : (towerInclBar L (dvd_of_eq_roof N ℓ ℓ' M hM).1).toRingHom.IsIntegral)
    (hu' : (towerSubstBar L (N * ℓ') ℓ (dvd_of_eq_roof N ℓ ℓ' M hM).2).toRingHom.IsIntegral)
    (D : Divisor L (laurentBaseChange L (modularFunctionFieldFull (N * ℓ')))),
    Divisor.pullbackAlong (heckeBetaBar L N ℓ) hβ
        (Divisor.pushforwardAlong (heckeAlphaBar L N ℓ') hα' D)
      = Divisor.pushforwardAlong (towerInclBar L (dvd_of_eq_roof N ℓ ℓ' M hM).1) hu
          (Divisor.pullbackAlong (towerSubstBar L (N * ℓ') ℓ (dvd_of_eq_roof N ℓ ℓ' M hM).2) hu' D)

end Exchange

end ModularCurve

end
