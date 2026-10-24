/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalSheafDef.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.RingTheory.Ideal.Cotangent

noncomputable section

open KaehlerDifferential

namespace CanonicalSheafDef

universe u v


/-- The property of being a standard smooth `R`-algebra of relative dimension `n`. -/
abbrev IsSmoothMorphismOfRelDim (n : ℕ) (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S] : Prop :=
  Algebra.IsStandardSmoothOfRelativeDimension n R S


/-- An `Algebra k A` is smooth of dimension `d` when its module of Kähler differentials
`Ω[A⁄k]` is free, finite, and has rank `d` over `A`. -/
class IsSmoothOfDimension (k : Type u) (A : Type v)
    [CommRing k] [CommRing A] [Algebra k A] (d : ℕ) : Prop where
  free : Module.Free A (Ω[A⁄k])
  finite : Module.Finite A (Ω[A⁄k])
  finrank_eq : Module.finrank A (Ω[A⁄k]) = d


/-- The canonical module ω_X = ∧^d Ω_X (Def 37, Lec 19): the `d`-th exterior power of the
module of Kähler differentials. -/
def canonicalModule (k : Type u) (A : Type v) [CommRing k] [CommRing A]
    [Algebra k A] (d : ℕ) : Submodule A (ExteriorAlgebra A (Ω[A⁄k])) :=
  ⋀[A]^d (Ω[A⁄k])


/-- The conormal module of an ideal `I ⊆ A`, namely `I / I²`. -/
abbrev conormalModule (A : Type u) [CommRing A] (I : Ideal A) : Type u :=
  I.Cotangent
