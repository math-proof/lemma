module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Axioms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

public import Theorem.v1.Atlas.TensorCategories.code.HopfAlgebra.Part3
public import Def.v1.Atlas.TensorCategories.code.CoradicalFiltration.Part8
public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.LinearAlgebra.TensorAlgebra.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct
public import Mathlib.RingTheory.Coalgebra.Hom
public import Mathlib.RingTheory.Smooth.Basic
public section
set_option maxHeartbeats 800000

open Coalgebra HopfAlgebra
open scoped TensorProduct

universe u v

/-- A coalgebra `(H, Δ, ε)` is cocommutative if the comultiplication is symmetric:
`τ ∘ Δ = Δ` for the flip `τ : H ⊗ H → H ⊗ H`. -/
class Coalgebra.IsCocommutative (R : Type u) (H : Type v)
    [CommSemiring R] [AddCommMonoid H] [Module R H] [Coalgebra R H] : Prop where
  cocomm : (TensorProduct.comm R H H).toLinearMap ∘ₗ (comul : H →ₗ[R] H ⊗[R] H) = comul

