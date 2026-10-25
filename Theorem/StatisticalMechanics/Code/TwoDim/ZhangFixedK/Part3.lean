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
import Def.StatisticalMechanics.Code.TwoDim.ZhangFixedK.Part3
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal


namespace StatMech.TwoDim

open StatMech.Lattice StatMech.Universality StatMech.Percolation

open StatMech.RSW.Box


theorem zfk_shift_mem_rightSquare_iff (N : ℕ) (x : Site 2) :
    x ∈ zfk_leftSquare N ↔ x + (![1, 0] : Site 2) ∈ zfk_rightSquare N := by
  have hR : rect (-(N : ℤ) + (![1, 0] : Site 2) 0)
        ((N : ℤ) + (![1, 0] : Site 2) 0)
        (-(N : ℤ) + (![1, 0] : Site 2) 1)
        ((N : ℤ) + (![1, 0] : Site 2) 1) = zfk_rightSquare N := by
    congr 1 <;> norm_num [zfk_rightSquare]
  rw [zfk_leftSquare, ← hR]
  exact cti_mem_rect_translate (-(N : ℤ)) N (-(N : ℤ)) N ![1, 0] x

end StatMech.TwoDim
