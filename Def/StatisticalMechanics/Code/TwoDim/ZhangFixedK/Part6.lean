/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.TwoDim.ZhangBKData.Part6
import Theorem.StatisticalMechanics.Code.Universality.FrameChangeIso.Part8
import Theorem.StatisticalMechanics.Code.Universality.CrossingReflection.Part4
import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part101
import Theorem.StatisticalMechanics.Code.Universality.KestenBXPWire
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangFixedK.Part5
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal


namespace StatMech.TwoDim

open StatMech.Lattice StatMech.Universality StatMech.Percolation

open StatMech.RSW.Box


def zfk_MergedArmPairEvent (k N : ℕ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  {omega | ∃ x ∈ box 2 k, ∃ y ∈ zfk_rightCentralBox k,
    (cluster 2 omega x).Infinite ∧ (cluster 2 omega y).Infinite ∧
      zfk_LeftArmFrom omega x N ∧ zfk_RightArmFrom omega y N ∧
        omega ∈ zbd_connectedWithinBox x y N}

end StatMech.TwoDim
