/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ClosedPointMorphism.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.ArithmeticGeometry.code.Divisors.Part11
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.Divisors
public import Theorem.v1.Atlas.ArithmeticGeometry.code.ClosedPointMorphism

@[expose] public section

open MulAction


namespace ClosedPoint

variable {G : Type*} [Group G]

variable {C₁ : Type*} {C₂ : Type*} [MulAction G C₁] [MulAction G C₂]

/-- Functoriality of closed points (Galois orbits) under a $G$-equivariant map of underlying sets. -/
def map (φ : C₁ → C₂)
    (hφ : ∀ (g : G) (P : C₁), φ (g • P) = g • φ P) :
    ClosedPoint G C₁ → ClosedPoint G C₂ :=
  Quotient.map φ (orbitRel_map_of_equivariant φ hφ)


end ClosedPoint
