/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionTouchingBondGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionPrismFaces.Part2
import Theorem.StatisticalMechanics.Code.IsingFK.HisingBoxClose.Part3
import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionTouchingBondGeometry.Part2


namespace StatMech.FrontierA

open StatMech StatMech.Lattice StatMech.Ising StatMech.IsingFK
  StatMech.Percolation


theorem oddPrismTouchIndexBond_mem (n : Nat) (q : OddPrismTouchIndex n) :
    oddPrismTouchIndexBond n q ∈ bondFinsetTouch 3 n := by
  let e := rectangularPrismSiteEquivSctBoxDobrushin n
  cases q with
  | xInternal x y z =>
      rw [oddPrismTouchIndexBond, hbx_mem_bondFinsetTouch_iff]
      refine ⟨?_, Or.inl (e ⟨⟨x.val, by omega⟩, y, z⟩).2⟩
      rw [hypercubicLattice_adj, Fin.sum_univ_three]
      simp [e]
  | yInternal x y z =>
      rw [oddPrismTouchIndexBond, hbx_mem_bondFinsetTouch_iff]
      refine ⟨?_, Or.inl (e ⟨x, ⟨y.val, by omega⟩, z⟩).2⟩
      rw [hypercubicLattice_adj, Fin.sum_univ_three]
      simp [e]
  | zInternal x y z =>
      rw [oddPrismTouchIndexBond, hbx_mem_bondFinsetTouch_iff]
      refine ⟨?_, Or.inl (e ⟨x, y, ⟨z.val, by omega⟩⟩).2⟩
      rw [hypercubicLattice_adj, Fin.sum_univ_three]
      simp [e]
  | xZero y z =>
      rw [oddPrismTouchIndexBond, hbx_mem_bondFinsetTouch_iff]
      exact ⟨adj_coordShift _ 0 false, Or.inl (e ⟨0, y, z⟩).2⟩
  | xLast y z =>
      rw [oddPrismTouchIndexBond, hbx_mem_bondFinsetTouch_iff]
      exact ⟨adj_coordShift _ 0 true, Or.inl
        (e ⟨Fin.last (2 * n), y, z⟩).2⟩
  | yZero x z =>
      rw [oddPrismTouchIndexBond, hbx_mem_bondFinsetTouch_iff]
      exact ⟨adj_coordShift _ 1 false, Or.inl (e ⟨x, 0, z⟩).2⟩
  | yLast x z =>
      rw [oddPrismTouchIndexBond, hbx_mem_bondFinsetTouch_iff]
      exact ⟨adj_coordShift _ 1 true, Or.inl
        (e ⟨x, Fin.last (2 * n), z⟩).2⟩
  | zZero x y =>
      rw [oddPrismTouchIndexBond, hbx_mem_bondFinsetTouch_iff]
      exact ⟨adj_coordShift _ 2 true, Or.inl (e ⟨x, y, 0⟩).2⟩
  | zLast x y =>
      rw [oddPrismTouchIndexBond, hbx_mem_bondFinsetTouch_iff]
      exact ⟨adj_coordShift _ 2 false, Or.inl
        (e ⟨x, y, Fin.last (2 * n)⟩).2⟩


end StatMech.FrontierA
