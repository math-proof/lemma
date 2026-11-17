/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CotangentExactSequence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Smooth.Basic

public section

noncomputable section

open scoped TensorProduct

open KaehlerDifferential

universe u

section CotangentExactSequence

variable (R : Type u) [CommRing R]

variable {A B : Type*} [CommRing A] [CommRing B]

variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

end CotangentExactSequence
end
