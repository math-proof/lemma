import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.Data.Finite.Card
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

noncomputable section

open UpperHalfPlane

universe u

namespace ModularFormClass

def qCoeff (f : ℍ → ℂ) (n : ℕ) : ℂ :=
  (qExpansion 1 f).coeff n

end ModularFormClass

namespace CuspForm

open ModularFormClass

structure IsNormalizedEigenform {N : ℕ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    Prop where

  qCoeff_one : qCoeff f 1 = 1

  qCoeff_mul_of_coprime : ∀ m n : ℕ, m.Coprime n →
    qCoeff f (m * n) = qCoeff f m * qCoeff f n

  qCoeff_prime_pow_of_not_dvd : ∀ p r : ℕ, p.Prime → ¬ p ∣ N →
    qCoeff f (p ^ (r + 2)) = qCoeff f p * qCoeff f (p ^ (r + 1)) - p * qCoeff f (p ^ r)

  qCoeff_prime_pow_of_dvd : ∀ p r : ℕ, p.Prime → p ∣ N →
    qCoeff f (p ^ (r + 2)) = qCoeff f p * qCoeff f (p ^ (r + 1))

end CuspForm

namespace WeierstrassCurve

namespace Affine

variable {R : Type u} [CommRing R] {W' : Affine R}

private def Point.toOptionPair : W'.Point → Option (R × R)
  | .zero => none
  | .some x y _ => Option.some (x, y)

private lemma Point.toOptionPair_injective :
    Function.Injective (Point.toOptionPair (W' := W')) := by
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h <;>
    simp only [Point.toOptionPair, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  · rfl
  · obtain ⟨rfl, rfl⟩ := h; rfl

instance Point.instFinite [Finite R] : Finite W'.Point :=
  Finite.of_injective _ Point.toOptionPair_injective

end Affine

section Card

variable {F : Type u} [CommRing F] (W : WeierstrassCurve F)

def card : ℕ := Nat.card W.toAffine.Point

def traceOfFrobenius : ℤ := (Nat.card F : ℤ) + 1 - (W.card : ℤ)

end Card

def reductionMod (W : WeierstrassCurve ℤ) (p : ℕ) : WeierstrassCurve (ZMod p) :=
  W.map (Int.castRingHom (ZMod p))

def apOfModel (W : WeierstrassCurve ℤ) (p : ℕ) : ℤ :=
  (W.reductionMod p).traceOfFrobenius

def IsGoodPrimeFor (W : WeierstrassCurve ℤ) (p : ℕ) : Prop :=
  ¬ (p : ℤ) ∣ W.Δ

def IsSemistableModel (W : WeierstrassCurve ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → (p : ℤ) ∣ W.Δ → ¬ (p : ℤ) ∣ W.c₄

def IsIntegralModelOf (W : WeierstrassCurve ℤ) (E : WeierstrassCurve ℚ) : Prop :=
  ∃ C : VariableChange ℚ, C • E = W.map (Int.castRingHom ℚ)

open CuspForm

def IsModularModelOfLevel (W : WeierstrassCurve ℤ) (N : ℕ) : Prop :=
  ∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) 2, f.IsNormalizedEigenform ∧
    ∀ p : ℕ, p.Prime → W.IsGoodPrimeFor p → ¬ p ∣ N →
      ModularFormClass.qCoeff f p = (W.apOfModel p : ℂ)

def IsModularModel (W : WeierstrassCurve ℤ) : Prop :=
  ∃ N : ℕ, 0 < N ∧ W.IsModularModelOfLevel N

def IsModular (E : WeierstrassCurve ℚ) : Prop :=
  ∃ W : WeierstrassCurve ℤ, W.IsIntegralModelOf E ∧ W.IsModularModel

end WeierstrassCurve

end
