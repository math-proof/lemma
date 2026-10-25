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
import Def.StatisticalMechanics.Code.TwoDim.ZhangFixedK.Part4
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal


namespace StatMech.TwoDim

open StatMech.Lattice StatMech.Universality StatMech.Percolation

open StatMech.RSW.Box


theorem zfk_connectedWithin_shiftRight_iff
    (omega : ConfigSpace (Sym2 (Site 2))) (N : ℕ) (x y : Site 2)
    (hx : x ∈ zfk_leftSquare N) (hy : y ∈ zfk_leftSquare N) :
    ConnectedWithin 2 (translateConfig (![1, 0] : Site 2) omega)
        (zfk_leftSquare N) ⟨x, hx⟩ ⟨y, hy⟩ ↔
      ConnectedWithin 2 omega (zfk_rightSquare N)
        ⟨x + ![1, 0], (zfk_shift_mem_rightSquare_iff N x).mp hx⟩
        ⟨y + ![1, 0], (zfk_shift_mem_rightSquare_iff N y).mp hy⟩ := by
  constructor
  · intro h
    exact h.map (zfk_shiftRightHom N omega)
  · intro h
    have hm := h.map (zfk_shiftRightHomInv N omega)
    convert hm using 1 <;> apply Subtype.ext <;> simp [zfk_shiftRightHomInv] <;>
      apply funext <;> intro i <;> fin_cases i <;> rfl


end StatMech.TwoDim
