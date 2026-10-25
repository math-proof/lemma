/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/EdgeExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset


namespace BooleanAnalysis

structure WeightedRegularGraph (V : Type*) [Fintype V] [DecidableEq V] where
  weight : V → V → ℝ
  degree : ℝ
  weight_nonneg : ∀ x y, 0 ≤ weight x y
  degree_pos : 0 < degree
  regular : ∀ x, ∑ y : V, weight x y = degree

end BooleanAnalysis
