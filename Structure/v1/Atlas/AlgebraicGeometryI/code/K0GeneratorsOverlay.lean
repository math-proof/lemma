/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/K0GeneratorsOverlay.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.GroupTheory.QuotientGroup.Basic


namespace K0Gen

/-- Axiomatic data for `K^0(Coh X)` of a smooth curve: a type of coherent sheaves with
rank/degree invariants additive in short exact sequences, including the distinguished
classes `O_X` (rank one, degree zero) and `O_x` (rank zero, degree one). -/
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

end K0Gen
