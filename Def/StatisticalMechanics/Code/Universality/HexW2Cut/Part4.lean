/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Cut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexWall3.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexInfraDisplacement.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexInfraCut
import Theorem.StatisticalMechanics.Code.Universality.HexSurgerySeams.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexInjections.Part7
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexW2Cut.Part3


namespace StatMech.Universality

open HexWalk List Filter

open scoped BigOperators Real


noncomputable def hexW2_prefixBridge (h0 : ℤ) (ts : List ℤ)
    (hone : (1 : ℝ) ≤ hexW2_partialDisp h0 ts (hexW2_cutPos h0 ts)) : HexBridge where
  width := hexW2_cutWidth h0 ts
  width_pos := hexW2_cutWidth_pos h0 ts hone
  content := ts.take (hexW2_cutPos h0 ts)
  content_ne := hexW2_prefix_content_ne h0 ts hone

end StatMech.Universality
