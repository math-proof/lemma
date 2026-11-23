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
public import Structure.v1.Atlas.AlgebraicGeometryI.code.ResidueSumZero

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial Finset BigOperators HahnSeries Classical
  IsDedekindDomain

universe u

variable {k : Type u} [Field k]

namespace ResidueSumZero

/-- The local Laurent expansion of `ω` at its `j`-th pole: a pure simple pole
with coefficient `c_j`. -/
noncomputable def PartialFracDiff.localExpansionAtPole
    (ω : PartialFracDiff k) (j : Fin ω.n) : LaurentSeries k :=
  simplePole (ω.c j)

/-- The local Laurent expansion at infinity: a simple pole with residue equal
to `−Σ c_i`, enforcing the residue theorem on `ℙ¹`. -/
noncomputable def PartialFracDiff.localExpansionAtInf
    (ω : PartialFracDiff k) : LaurentSeries k :=
  simplePole (-(∑ i, ω.c i))


end ResidueSumZero
end
