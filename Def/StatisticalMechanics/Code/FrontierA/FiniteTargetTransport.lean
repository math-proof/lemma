/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FiniteTargetTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
open Set
open scoped ENNReal


namespace StatMech.FrontierA

variable {alpha : Type*}


noncomputable def finiteTargetTransport (C : Set alpha) (N : Finset alpha)
    (x y : alpha) : ℝ≥0∞ := by
  classical
  exact if x ∈ C ∧ y ∈ N then ((N.card : ℝ≥0∞)⁻¹) else 0


end StatMech.FrontierA
