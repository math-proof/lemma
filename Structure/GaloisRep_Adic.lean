import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Instance.GaloisRep_Residual
import Structure.GaloisRep_ResidualEquiv

open scoped TensorProduct

def GaloisActionIsAdicContinuous (A : Type) [CommRing A] [IsLocalRing A]
    {V : Type} [AddCommGroup V] [Module A V]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End A V) : Prop :=
  ∀ n : ℕ, ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
    ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ x = x) →
      ∀ v : V, ρ σ v - v ∈ (IsLocalRing.maximalIdeal A ^ n) • (⊤ : Submodule A V)

structure GaloisRepAdic (A : Type) [CommRing A] [IsLocalRing A] : Type 1 where

  V : Type
  [instAddCommGroup : AddCommGroup V]
  [instModule : Module A V]
  [instFree : Module.Free A V]
  [instFinite : Module.Finite A V]

  finrank_eq : Module.finrank A V = 2

  ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End A V

  isAdicContinuous : GaloisActionIsAdicContinuous A ρ

attribute [instance] GaloisRepAdic.instAddCommGroup GaloisRepAdic.instModule
  GaloisRepAdic.instFree GaloisRepAdic.instFinite

namespace GaloisRepAdic

variable {A : Type} [CommRing A] [IsLocalRing A]


structure Equiv (ρ₁ ρ₂ : GaloisRepAdic A) where

  toLinearEquiv : ρ₁.V ≃ₗ[A] ρ₂.V

  map_apply : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : ρ₁.V),
    toLinearEquiv (ρ₁.ρ σ x) = ρ₂.ρ σ (toLinearEquiv x)


namespace Equiv


end Equiv

end GaloisRepAdic

namespace GaloisRepAdic

variable {A : Type} [CommRing A] [IsLocalRing A]


end GaloisRepAdic
