/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWInsetLeftSourceAttachment.Part3
import Def.StatisticalMechanics.Code.Universality.RSWInsetSourceFloor
open Finset SimpleGraph Set MeasureTheory


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

@[simp] theorem rlc_affineFlipY_zero (k : Int) (x : Site 2) :
    rlc_affineFlipY k x 0 = x 0 := by
  simp [rlc_affineFlipY, rlc_affineFlipYFun]

@[simp] theorem rlc_affineFlipY_one (k : Int) (x : Site 2) :
    rlc_affineFlipY k x 1 = k - x 1 := by
  simp [rlc_affineFlipY, rlc_affineFlipYFun]

@[simp] theorem rlc_affineFlipY_involutive (k : Int) (x : Site 2) :
    rlc_affineFlipY k (rlc_affineFlipY k x) = x := by
  exact (rlc_affineFlipY k).left_inv x

theorem rlc_adj_affineFlipY (k : Int) (x y : Site 2) :
    (hypercubicLattice 2).Adj x y ↔
      (hypercubicLattice 2).Adj (rlc_affineFlipY k x) (rlc_affineFlipY k y) := by
  rw [hypercubicLattice_adj, hypercubicLattice_adj,
    Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [rlc_affineFlipY_zero, rlc_affineFlipY_one]
  rw [show (k - x 1) - (k - y 1) = -(x 1 - y 1) by ring,
    Int.natAbs_neg]

end
end StatMech.Universality
