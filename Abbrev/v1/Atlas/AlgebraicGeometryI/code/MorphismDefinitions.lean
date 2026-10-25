/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/MorphismDefinitions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.Order.KrullDimension
import Mathlib.RingTheory.KrullDimension.Basic
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.FiniteMorphismDimension
open PrimeSpectrum


namespace MorphismDefinitions

section FiniteAlgebra

variable (B A : Type*) [CommRing B] [CommRing A] [Algebra B A]

/-- A `B`-algebra `A` is finite if `A` is a finitely generated `B`-module. -/
abbrev IsFiniteAlgebra : Prop := Module.Finite B A

end FiniteAlgebra
end MorphismDefinitions
