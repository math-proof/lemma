/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/MorphismDefinitions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.Order.KrullDimension
public import Mathlib.RingTheory.KrullDimension.Basic
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.FiniteMorphismDimension
@[expose] public section

open PrimeSpectrum


namespace MorphismDefinitions

section FiniteAlgebra

variable (B A : Type*) [CommRing B] [CommRing A] [Algebra B A]

/-- A `B`-algebra `A` is finite if `A` is a finitely generated `B`-module. -/
abbrev IsFiniteAlgebra : Prop := Module.Finite B A

end FiniteAlgebra
end MorphismDefinitions
