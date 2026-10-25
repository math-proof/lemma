/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareCaratheodory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBoundaryScaledDomain.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCaratheodoryApproximation.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareCaratheodory


namespace StatMech.Universality

open Filter Set Topology Metric

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC
  StatMech.FrontierD

noncomputable section

theorem fkIsingExpandingSquareSide_pos (k : Nat) :
    0 < fkIsingExpandingSquareSide k := by
  simp [fkIsingExpandingSquareSide]

theorem fkIsingExpandingSquareScale_pos (k : Nat) :
    0 < fkIsingExpandingSquareScale k := by
  simp [fkIsingExpandingSquareScale]
  positivity

theorem fkIsingExpandingSquareMesh_pos (k : Nat) :
    0 < fkIsingExpandingSquareMesh k := by
  simp [fkIsingExpandingSquareMesh, fkIsingExpandingSquareScale]
  positivity

theorem fkIsingExpandingSquareMesh_tendsto_zero :
    Tendsto fkIsingExpandingSquareMesh atTop (nhds 0) := by
  have hadd : Tendsto (fun k : Nat ↦ k + 1) atTop atTop :=
    tendsto_add_atTop_nat 1
  have hinv : Tendsto (fun k : Nat ↦ (1 : Real) / (k + 1 : Nat))
      atTop (nhds 0) := tendsto_one_div_atTop_nhds_zero_nat.comp hadd
  change Tendsto (fun k : Nat ↦ (4 : Real) * (1 / (k + 1 : Nat)))
    atTop (nhds 0)
  convert (tendsto_const_nhds.mul hinv :
      Tendsto (fun k : Nat ↦ (4 : Real) * (1 / (k + 1 : Nat)))
        atTop (nhds (4 * 0))) using 1 <;> norm_num


end
end StatMech.Universality
