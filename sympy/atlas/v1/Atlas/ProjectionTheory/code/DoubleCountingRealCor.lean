/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/DoubleCountingRealCor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.ProjectionTheory.code.DoubleCountingReal
import Lemma.Real.Atlas.v1.ProjectionTheory.code.DoubleCountingReal
import sympy.atlas.v1.Atlas.ProjectionTheory.code.HausdorffSpacing

open Finset BigOperators

namespace ProjectionTheory

/-- A `DoubleCountingRealSetup` augmented with the Hausdorff (a.k.a. dimension)
spacing hypotheses on both `X` and `D`: the covering numbers obey
`N_X(R^β) ≲ |X|^β` and `N_D(R^{β-1}) ≲ |D|^β` for every `β ∈ [0, 1]`. -/
structure DoubleCountingRealHausdorffSetup extends DoubleCountingRealSetup where
  C_X : ℝ
  hC_X_pos : 0 < C_X
  hHausdorff_X : ∀ β : ℝ, 0 ≤ β → β ≤ 1 →
    (N_X (R ^ β) : ℝ) ≤ C_X * (cardX : ℝ) ^ β
  C_D : ℝ
  hC_D_pos : 0 < C_D
  hHausdorff_D : ∀ β : ℝ, 0 ≤ β → β ≤ 1 →
    (N_D (R ^ (β - 1)) : ℝ) ≤ C_D * (cardD : ℝ) ^ β
