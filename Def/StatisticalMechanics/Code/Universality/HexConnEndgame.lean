/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnEndgame.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.SAW


namespace StatMech.Universality

open Filter Topology

open scoped Topology Real NNReal


noncomputable def hexChiE : ℝ := 1 / Real.sqrt (2 + Real.sqrt 2)


noncomputable def hexCl : ℝ := Real.cos (3 * Real.pi / 8)


noncomputable def hexCt : ℝ := Real.cos (Real.pi / 4)


end StatMech.Universality
