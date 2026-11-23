/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec24RiemannRochSerre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.Lemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Field.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Structure.v1.Atlas.AlgebraicGeometryI.code.SerreDualityStatement
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.SerreDualityStatement
public import Def.v1.Atlas.AlgebraicGeometryI.code.Lec24RiemannRochSerre.Part4
set_option maxHeartbeats 800000


@[expose] public noncomputable section

namespace Lec24

namespace SmoothCompleteCurveWithSheaves

variable (X : SmoothCompleteCurveWithSheaves)

/-- The Grothendieck group `K_0(Coh X)`: the free abelian group on coherent sheaves modulo
the short-exact-sequence relations. -/
abbrev K0Coh (X : SmoothCurveK0Data) : Type :=
  FreeAbelianGroup X.CohSheaf ⧸ sesRelations X

end SmoothCompleteCurveWithSheaves
end Lec24
end
