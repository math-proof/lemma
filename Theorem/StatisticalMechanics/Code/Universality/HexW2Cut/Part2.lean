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
import Def.StatisticalMechanics.Code.Universality.HexW2Cut.Part2


namespace StatMech.Universality

open HexWalk List Filter

open scoped BigOperators Real


theorem hexW2_cutPos_le (h0 : ℤ) (ts : List ℤ) :
    hexW2_cutPos h0 ts ≤ ts.length :=
  (hexW2_exists_firstArgmax h0 ts).choose_spec.1


theorem hexW2_cutPos_max (h0 : ℤ) (ts : List ℤ) (k : ℕ) (hk : k ≤ ts.length) :
    hexW2_partialDisp h0 ts k ≤ hexW2_partialDisp h0 ts (hexW2_cutPos h0 ts) :=
  (hexW2_exists_firstArgmax h0 ts).choose_spec.2.1 k hk


theorem hexW2_cutPos_first (h0 : ℤ) (ts : List ℤ) (k : ℕ) (hk : k < hexW2_cutPos h0 ts) :
    hexW2_partialDisp h0 ts k < hexW2_partialDisp h0 ts (hexW2_cutPos h0 ts) :=
  (hexW2_exists_firstArgmax h0 ts).choose_spec.2.2 k hk


theorem hexW2_prefix_reachesWidth (a : ℂ) (h0 : ℤ) (T : ℕ) (ts : List ℤ)
    (hT : (T : ℝ) ≤ hexW2_partialDisp h0 ts (hexW2_cutPos h0 ts)) :
    hexWall3_ReachesWidth a h0 T (ts.take (hexW2_cutPos h0 ts)) :=
  hexInfra_prefix_reachesWidth a h0 T ts (hexW2_cutPos h0 ts) hT


end StatMech.Universality
