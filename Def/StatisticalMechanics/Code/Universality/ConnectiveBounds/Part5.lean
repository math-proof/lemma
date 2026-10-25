/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectiveBounds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.SAW
import Theorem.StatisticalMechanics.Code.Universality.ConnectiveBounds.Part4


namespace StatMech.Universality

open Filter Topology Finset

open scoped Topology

open Classical


noncomputable def zdSAWCountR (d n : ℕ) : ℝ := (zdSAWCount d n : ℝ)

end StatMech.Universality
