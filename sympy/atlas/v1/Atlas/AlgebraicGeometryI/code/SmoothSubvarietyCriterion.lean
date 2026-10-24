/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothSubvarietyCriterion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.FinitePresentation

universe u v w

open scoped TensorProduct
open KaehlerDifferential Algebra

variable {R : Type u} {A : Type v} {B : Type w}
  [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

/-- Predicate asserting that the canonical map from the cotangent module of
the kernel `I = ker(A → B)` to `B ⊗_A Ω[A/R]` has a left inverse, i.e. that the
differentials of generators of `I` are linearly independent in `B ⊗_A Ω[A/R]`. -/
def HasLinearlyIndependentDifferentials (R : Type u) (A : Type v) (B : Type w)
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B] : Prop :=
  ∃ l : B ⊗[A] Ω[A⁄R] →ₗ[A] (RingHom.ker (algebraMap A B)).Cotangent,
    l ∘ₗ kerCotangentToTensor R A B = LinearMap.id
