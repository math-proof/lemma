/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/DoubleCountingReal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.ProjectionTheory.code.DoubleCountingReal.Part2
open Finset BigOperators


namespace ProjectionTheory

/-- The data for the SETUP of the real-version double-counting theorem: a scale
parameter `R ≥ 1`, the cardinalities `|X|` and `|D|` of a planar point set and a
direction set, the maximal projection size `S` (with `0 < S ≤ |X|`), and the multiscale
covering numbers `N_X(r)`, `N_D(ρ)` at radii `r, ρ`. -/
structure DoubleCountingRealSetup where
  R : ℝ
  hR : 1 ≤ R
  cardX : ℕ
  cardD : ℕ
  S : ℕ
  hS_pos : 0 < S
  hS_le : S ≤ cardX
  N_X : ℝ → ℕ
  N_D : ℝ → ℕ
  hN_X_le : ∀ r, N_X r ≤ cardX
  hN_D_le : ∀ ρ, N_D ρ ≤ cardD

end ProjectionTheory
