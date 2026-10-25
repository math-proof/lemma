/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripCountsClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexInfraDisplacement.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
import Theorem.StatisticalMechanics.Code.Universality.HexConnClosed
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


noncomputable def hsc_refl (a0 : ℂ) (h0 : ℤ) (z : ℂ) : ℂ :=
  a0 + (hexUnit h0)^2 * (starRingEnd ℂ) (z - a0)


end StatMech.Universality
