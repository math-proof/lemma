module
public import Mathlib.NumberTheory.RamificationInertia.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Discriminant
public import Def.v1.Atlas.AlgebraicGeometryI.code.CoherentSheavesCurves.Part2
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.CoherentSheavesCurves
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannHurwitz
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalDivisorDecomposition
public import Theorem.v1.Atlas.AlgebraicGeometryI.code.RiemannHurwitz
public import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalDivisorDecomposition.Part4
public import Def.v1.Atlas.AlgebraicGeometryI.code.RiemannHurwitzFormula.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzFormula.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open Ideal Module

namespace RiemannHurwitzFormula

section DVRRamification

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

variable {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]

variable [Algebra R S]

example : (2 : ℤ) * 2 - 2 = 2 * (-2) + 6 := by norm_num

example : (2 : ℤ) * 1 - 2 = 3 * (-2) + 6 := by norm_num

example : (2 : ℤ) * 3 - 2 = 2 * (2 * 2 - 2) + 0 := by norm_num

end DVRRamification
end RiemannHurwitzFormula
end
