/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ResidueSumZero.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.AlgebraicGeometryI.code.ResidueSum
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.ResidueSum
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.Kaehler.Basic
public import Structure.v1.Atlas.AlgebraicGeometryI.code.ResidueSumZero.Part2
@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial Finset BigOperators HahnSeries Classical
  IsDedekindDomain

universe u

variable {k : Type u} [Field k]

namespace ResidueSumZero

variable (C : SmoothProperCurve k)

instance : CommRing C.A := C.instCommRingA

instance : IsDomain C.A := C.instIsDomainA

instance : IsDedekindDomain C.A := C.instIsDedekindDomainA

instance : Algebra k C.A := C.instAlgebraKA

instance : Field C.K := C.instFieldK

instance : Algebra C.A C.K := C.instAlgebraAK

instance : IsFractionRing C.A C.K := C.instIsFractionRing

instance : Algebra k C.K := C.instAlgebraKK

instance : IsScalarTower k C.A C.K := C.instIsScalarTower

end ResidueSumZero
end
