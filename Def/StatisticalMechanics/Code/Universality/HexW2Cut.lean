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


namespace StatMech.Universality

open HexWalk List Filter

open scoped BigOperators Real


noncomputable def hexW2_partialDisp (h0 : ℤ) (ts : List ℤ) (k : ℕ) : ℝ :=
  hexInfra_stepReSum h0 (ts.take k)
    + (HexWalk.halfStep (hexInfra_headAccum h0 (ts.take k))).re


end StatMech.Universality
