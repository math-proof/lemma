/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4RadialDecay.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4DiagonalRate.Part3
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQConnectionSymmetry
import Theorem.StatisticalMechanics.Code.FK.RotationInvariance.Part3
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4RadialDecay
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation

noncomputable section

def fkQgt4CoordinateSignBoxSym (flip : Fin 2 -> Bool) : FK.BoxSym 2 where
  τ :=
    { toFun := fun x i => if flip i then -(x i) else x i
      invFun := fun x i => if flip i then -(x i) else x i
      left_inv := by
        intro x
        funext i
        cases h : flip i <;> simp [h]
      right_inv := by
        intro x
        funext i
        cases h : flip i <;> simp [h] }
  adj := by
    intro x y
    simp only [hypercubicLattice_adj, Equiv.coe_fn_mk]
    rw [show (∑ i,
        ((if flip i then -(x i) else x i) -
          (if flip i then -(y i) else y i)).natAbs) =
        ∑ i, (x i - y i).natAbs by
      apply Finset.sum_congr rfl
      intro i _
      cases h : flip i
      · simp [h]
      · simp only [h, Bool.true_eq, ↓reduceIte]
        rw [show -x i - -y i = -(x i - y i) by ring,
          Int.natAbs_neg]]
  box_mem := by
    intro n x
    simp only [mem_box, Equiv.coe_fn_mk]
    constructor <;> intro h i
    · simpa [show (if flip i then -x i else x i).natAbs = (x i).natAbs by
          cases hflip : flip i <;> simp [hflip]] using h i
    · simpa [show (if flip i then -x i else x i).natAbs = (x i).natAbs by
          cases hflip : flip i <;> simp [hflip]] using h i


def fkQgt4NonnegativeSite (x : Site 2) : Site 2 :=
  fun i => if x i < 0 then -x i else x i

end
end StatMech.FrontierD
