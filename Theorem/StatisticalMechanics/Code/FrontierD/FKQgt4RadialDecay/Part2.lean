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
import Def.StatisticalMechanics.Code.FrontierD.FKQgt4RadialDecay.Part2
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation

noncomputable section

theorem fkQgt4NonnegativeSite_apply (x : Site 2) (i : Fin 2) :
    fkQgt4NonnegativeSite x i = ((x i).natAbs : Int) := by
  by_cases h : x i < 0
  · rw [fkQgt4NonnegativeSite, if_pos h, ← Int.natAbs_neg]
    exact (Int.natAbs_of_nonneg (by linarith : 0 <= -x i)).symm
  · rw [fkQgt4NonnegativeSite, if_neg h]
    exact (Int.natAbs_of_nonneg (le_of_not_gt h)).symm

theorem fkQgt4CoordinateSignBoxSym_normalizes (x : Site 2) :
    (fkQgt4CoordinateSignBoxSym
      (fun i => decide (x i < 0))).τ x =
        fkQgt4NonnegativeSite x := by
  funext i
  simp only [fkQgt4CoordinateSignBoxSym, Equiv.coe_fn_mk]
  by_cases h : x i < 0 <;> simp [h, fkQgt4NonnegativeSite]


end
end StatMech.FrontierD
