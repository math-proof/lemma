import Lemma.Definitions.Def_ModularCurve_HeckeOperator
import Lemma.Definitions.Def_ModularCurve_DegeneracyTower

set_option autoImplicit false

namespace ModularCurve

open AlgebraicCurve

section Diagonal

variable (L : Type*) [Field L] [Algebra ℚ L] (N p : ℕ) [NeZero N] [NeZero p]

def HeckeDiagonalIdentity : Prop :=
  ∀ [HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull (N * p)))]
    [HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull (N * p * p)))]
    (hα : HeckeAlphaBarIntegral L N p) (hβ : HeckeBetaBarIntegral L N p)
    (hα₂ : HeckeAlphaBarIntegral L (N * p) p) (hβ₂ : HeckeBetaBarIntegral L (N * p) p)
    (σ : laurentBaseChange L (modularFunctionFieldFull (N * p)) ≃ₐ[L]
      laurentBaseChange L (modularFunctionFieldFull (N * p)))
    (_ : σ.toAlgHom.comp (heckeBetaBar L N p) = heckeAlphaBar L N p)
    (hσi : σ.toAlgHom.toRingHom.IsIntegral)
    (D : Divisor L (laurentBaseChange L (modularFunctionFieldFull (N * p)))),
    Divisor.pullbackAlong (heckeBetaBar L N p) hβ
        (Divisor.pushforwardAlong (heckeAlphaBar L N p) hα D)
      = heckeDivBar (N := N * p) (ℓ := p) hα₂ hβ₂ D
        + Divisor.pushforwardAlong σ.toAlgHom hσi D

end Diagonal

section BetaExchange

variable (L : Type*) [Field L] [Algebra ℚ L] (N ℓ ℓ' M : ℕ) [NeZero N] [NeZero ℓ] [NeZero ℓ']
  [NeZero M]

omit [NeZero N] [NeZero ℓ] [NeZero ℓ'] [NeZero M] in

theorem dvd_of_eq_roof_beta (hM : M = N * ℓ * ℓ') : N * ℓ * ℓ' ∣ M ∧ N * ℓ' * ℓ ∣ M :=
  ⟨⟨1, by rw [hM, mul_one]⟩, ⟨1, by rw [hM]; ring⟩⟩

def HeckeBetaExchangeAt (hM : M = N * ℓ * ℓ') : Prop :=
  ∀ [HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull (N * ℓ)))]
    [HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull M))]
    (hβ : (heckeBetaBar L N ℓ).toRingHom.IsIntegral)
    (hβ' : (heckeBetaBar L N ℓ').toRingHom.IsIntegral)
    (hu : (towerSubstBar L (N * ℓ) ℓ' (dvd_of_eq_roof_beta N ℓ ℓ' M hM).1).toRingHom.IsIntegral)
    (hu' : (towerSubstBar L (N * ℓ') ℓ (dvd_of_eq_roof_beta N ℓ ℓ' M hM).2).toRingHom.IsIntegral)
    (D : Divisor L (laurentBaseChange L (modularFunctionFieldFull (N * ℓ')))),
    Divisor.pullbackAlong (heckeBetaBar L N ℓ) hβ
        (Divisor.pushforwardAlong (heckeBetaBar L N ℓ') hβ' D)
      = Divisor.pushforwardAlong (towerSubstBar L (N * ℓ) ℓ'
            (dvd_of_eq_roof_beta N ℓ ℓ' M hM).1) hu
          (Divisor.pullbackAlong (towerSubstBar L (N * ℓ') ℓ
            (dvd_of_eq_roof_beta N ℓ ℓ' M hM).2) hu' D)

end BetaExchange

end ModularCurve
