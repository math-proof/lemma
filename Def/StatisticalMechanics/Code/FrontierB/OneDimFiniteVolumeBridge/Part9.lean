/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.OneDimTransferPerron
import Theorem.StatisticalMechanics.Code.Ising.FVConsistencyProve.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ContourCountInjection.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.OneDimFiniteVolumeBridge.Part8
open scoped BigOperators
open Finset Matrix


namespace StatMech.FrontierB

open StatMech.Lattice StatMech.Ising StatMech.FrontierC


noncomputable def box1EquivFin (n : ℕ) : {x // x ∈ box 1 n} ≃ Fin (2 * n + 1) where
  toFun x := ⟨(site1Coord x.1 + n).toNat, by
    have hx := (site1_mem_box_iff (site1Coord x.1) n).mp (by
      simpa only [site1_site1Coord] using x.2)
    omega⟩
  invFun k := ⟨site1 ((k : ℤ) - n), (site1_mem_box_iff _ _).mpr (by
    have hk := k.2
    constructor <;> omega)⟩
  left_inv x := by
    apply Subtype.ext
    change site1 ((((site1Coord x.1 + n).toNat : ℕ) : ℤ) - n) = x.1
    rw [← site1_site1Coord x.1]
    congr 1
    have hx := (site1_mem_box_iff (site1Coord x.1) n).mp (by
      simpa only [site1_site1Coord] using x.2)
    have hnonneg : 0 ≤ site1Coord x.1 + (n : ℤ) := by omega
    simp only [site1Coord_site1]
    rw [Int.toNat_of_nonneg hnonneg]
    ring
  right_inv k := by
    apply Fin.ext
    simp only [site1Coord_site1]
    have hk := k.2
    omega


def boolEquivFin2 : Bool ≃ Fin 2 where
  toFun := boolTransferState
  invFun s := if s = 0 then true else false
  left_inv b := by cases b <;> simp [boolTransferState]
  right_inv s := by fin_cases s <;> simp [boolTransferState]


noncomputable def interiorStateEquiv (n : ℕ) :
    ({x // x ∈ box 1 n} → Bool) ≃ (Fin (2 * n + 1) → Fin 2) :=
  Equiv.arrowCongr (box1EquivFin n) boolEquivFin2

end StatMech.FrontierB
