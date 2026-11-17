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
public import Def.v1.Atlas.AlgebraicGeometryI.code.Lec24RiemannRochSerre.Part3
set_option maxHeartbeats 800000


public noncomputable section

namespace Lec24

namespace SmoothCompleteCurveWithSheaves

variable (X : SmoothCompleteCurveWithSheaves)

/-- Axiomatic data for computing `K_0(Coh X)` on a smooth curve: a class of sheaves with
rank and degree functions, short exact sequences, plus designated structure sheaf and
skyscraper-at-a-point with the expected rank/degree values. -/
structure SmoothCurveK0Data where
  CohSheaf : Type
  rank : CohSheaf → ℕ
  deg : CohSheaf → ℤ
  SES : CohSheaf → CohSheaf → CohSheaf → Prop
  O_X : CohSheaf
  O_x : CohSheaf
  O_X_rank : rank O_X = 1
  O_X_deg : deg O_X = 0
  O_x_rank : rank O_x = 0
  O_x_deg : deg O_x = 1
  rank_additive : ∀ A B C, SES A B C → rank B = rank A + rank C
  deg_additive : ∀ A B C, SES A B C → deg B = deg A + deg C

end SmoothCompleteCurveWithSheaves
end Lec24
end
