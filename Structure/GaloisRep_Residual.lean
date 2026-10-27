import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.FieldTheory.Finiteness
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

set_option autoImplicit false

noncomputable section

open scoped TensorProduct
open Polynomial

def GaloisFactorsThroughFiniteLevel {M : Type} [MulOneClass M]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* M) : Prop :=
  ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
    ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ x = x) → ρ σ = 1

structure ResidualGaloisRep (k : Type) [Field k] : Type 1 where

  V : Type
  [instAddCommGroup : AddCommGroup V]
  [instModule : Module k V]

  finrank_eq : Module.finrank k V = 2

  ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End k V

  factorsThroughFiniteLevel : GaloisFactorsThroughFiniteLevel ρ

attribute [instance] ResidualGaloisRep.instAddCommGroup ResidualGaloisRep.instModule

instance ResidualGaloisRep.instModuleFinite {k : Type} [Field k] (ρ : ResidualGaloisRep k) :
    Module.Finite k ρ.V :=
  Module.finite_of_finrank_eq_succ ρ.finrank_eq

namespace ResidualGaloisRep

variable {k : Type} [Field k]


end ResidualGaloisRep


end
