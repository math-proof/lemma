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
public import Theorem.v1.Atlas.AlgebraicGeometryI.code.ResidueSumZero

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial Finset BigOperators HahnSeries Classical
  IsDedekindDomain

universe u

variable {k : Type u} [Field k]

namespace ResidueSumZero

/-- The simple pole `c · t^{-1}`, the basic Laurent series with residue `c`. -/
noncomputable def simplePole (c : k) : LaurentSeries k :=
  HahnSeries.single (-1 : ℤ) c

/-- The residue assembled as a `k`-linear map `LaurentSeries k →ₗ[k] k`. -/
noncomputable def laurentResidueLinearMap : LaurentSeries k →ₗ[k] k where
  toFun := laurentResidue
  map_add' := laurentResidue_add
  map_smul' c f := by simp [laurentResidue_smul]


end ResidueSumZero
end
