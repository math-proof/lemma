import Mathlib
import Def.FormalGroup_NSeries

set_option autoImplicit false

noncomputable section

namespace FormalGroup

variable {T : Type*} [CommRing T] [UniformSpace T]

def linComb (F : FormalGroup T) (x₀ x₁ : T) (a b : ℕ) : T :=
  F.eval (F.evalNSMul a x₀) (F.evalNSMul b x₁)

def drinfeldDivisor (F : FormalGroup T) (q : ℕ) (x₀ x₁ : T) : PowerSeries T :=
  ∏ a ∈ Finset.range q, ∏ b ∈ Finset.range q, (PowerSeries.X - PowerSeries.C (F.linComb x₀ x₁ a b))

def IsDrinfeldBasis (F : FormalGroup T) (q : ℕ) (x₀ x₁ : T) : Prop :=
  ∃ u : PowerSeries T, IsUnit u ∧ F.nthSeries q = u * F.drinfeldDivisor q x₀ x₁

def baseAct (F : FormalGroup T) (g : Matrix (Fin 2) (Fin 2) ℕ) (x₀ x₁ : T) : T × T :=
  (F.linComb x₀ x₁ (g 0 0) (g 1 0), F.linComb x₀ x₁ (g 0 1) (g 1 1))


section Adic

variable {T : Type*} [CommRing T]

def linCombAdic (F : FormalGroup T) (I : Ideal T) (x₀ x₁ : T) (a b : ℕ) : T :=
  letI : WithIdeal T := ⟨I⟩
  F.linComb x₀ x₁ a b

def drinfeldDivisorAdic (F : FormalGroup T) (I : Ideal T) (q : ℕ) (x₀ x₁ : T) : PowerSeries T :=
  letI : WithIdeal T := ⟨I⟩
  F.drinfeldDivisor q x₀ x₁

def IsDrinfeldBasisAdic (F : FormalGroup T) (I : Ideal T) (q : ℕ) (x₀ x₁ : T) : Prop :=
  letI : WithIdeal T := ⟨I⟩
  F.IsDrinfeldBasis q x₀ x₁

def baseActAdic (F : FormalGroup T) (I : Ideal T) (g : Matrix (Fin 2) (Fin 2) ℕ) (x₀ x₁ : T) : T × T :=
  letI : WithIdeal T := ⟨I⟩
  F.baseAct g x₀ x₁

end Adic

end FormalGroup

end
