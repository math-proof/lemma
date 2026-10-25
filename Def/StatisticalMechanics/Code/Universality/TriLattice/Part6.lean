/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.SAW
import Theorem.StatisticalMechanics.Code.Universality.TriLattice.Part5


namespace StatMech.Universality

open Filter Topology Finset

open scoped Topology

open Classical


noncomputable def triSAWCountR (n : ℕ) : ℝ := (triSAWCount n : ℝ)

end StatMech.Universality
