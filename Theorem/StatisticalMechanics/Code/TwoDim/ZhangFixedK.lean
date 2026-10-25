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
import Def.StatisticalMechanics.Code.TwoDim.ZhangFixedK
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal


namespace StatMech.TwoDim

open StatMech.Lattice StatMech.Universality StatMech.Percolation

open StatMech.RSW.Box


theorem zfk_rot_connectedWithin_box_iff
    (omega : ConfigSpace (Sym2 (Site 2))) (N : ℕ) (x y : box 2 N) :
    ConnectedWithin 2 (kdi_rotConfig omega) (box 2 N) x y ↔
      ConnectedWithin 2 omega (box 2 N)
        ⟨rot90Inv x, rot90Inv_mem_box N x.2⟩
        ⟨rot90Inv y, rot90Inv_mem_box N y.2⟩ := by
  exact (zfk_rotBoxIso omega N).reachable_iff.symm

end StatMech.TwoDim
