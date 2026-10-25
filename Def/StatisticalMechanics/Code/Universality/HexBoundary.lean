/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexVertex.Part5


namespace StatMech.Universality

open Complex Filter Topology

open scoped Topology Real BigOperators


noncomputable def hexBdryCl : ℝ := Real.cos (3 * Real.pi / 8)


noncomputable def hexBdryCt : ℝ := Real.cos (Real.pi / 4)


end StatMech.Universality
