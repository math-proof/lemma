/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ResidueSumZero.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.ResidueSum
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.ResidueSum
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Over
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Kaehler.Basic
import Theorem.v1.Atlas.AlgebraicGeometryI.code.ResidueSumZero


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
