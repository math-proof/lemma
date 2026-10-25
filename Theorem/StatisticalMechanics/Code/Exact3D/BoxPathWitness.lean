/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoxPathWitness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
import Theorem.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
open Filter


namespace StatMech

namespace Exact3D

open StatMech.Lattice


theorem boxGraph_update_mem_box {d n : ℕ} {x : Site d}
    (hx : x ∈ box d n) (j : Fin d) {a : ℤ} (ha : a.natAbs ≤ n) :
    Function.update x j a ∈ box d n :=
  Percolation.update_mem_box hx j ha


theorem boxGraph_adj_update_succ {d n : ℕ} {x : Site d}
    (hx : x ∈ box d n) (j : Fin d) {a : ℤ}
    (ha : a.natAbs ≤ n) (ha1 : (a + 1).natAbs ≤ n) :
    (FK.boxGraph d n).Adj
      ⟨Function.update x j a, boxGraph_update_mem_box hx j ha⟩
      ⟨Function.update x j (a + 1), boxGraph_update_mem_box hx j ha1⟩ := by
  simpa [FK.boxGraph] using Lattice.adj_update_succ x j a


theorem boxGraph_adj_boxVertStrictSectorPredecessor3
    {n : ℕ} (v : FK.boxVerts 3 n)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3))) :
    (FK.boxGraph 3 n).Adj
      (boxVertStrictSectorPredecessor3 v hvwedge hlt) v := by
  change (hypercubicLattice 3).Adj
    ((boxVertStrictSectorPredecessor3 v hvwedge hlt : FK.boxVerts 3 n) :
      Lattice.Site 3) (v : Lattice.Site 3)
  rw [hypercubicLattice_adj, Fin.sum_univ_three]
  rcases boxVertStrictSectorPredecessor3_hasCoords v hvwedge hlt with
    ⟨hw0, hw1, hw2⟩
  simp [hw0, hvwedge.1, hw1, hw2]


theorem boxGraph_adj_boxVertStrictSectorYPredecessor3
    {n : ℕ} (v : FK.boxVerts 3 n)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) :
    (FK.boxGraph 3 n).Adj
      (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) v := by
  change (hypercubicLattice 3).Adj
    ((boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos :
      FK.boxVerts 3 n) : Lattice.Site 3) (v : Lattice.Site 3)
  rw [hypercubicLattice_adj, Fin.sum_univ_three]
  rcases boxVertStrictSectorYPredecessor3_hasCoords
    v hvwedge hlt hypos with
    ⟨hw0, hw1, hw2⟩
  simp [hw0, hvwedge.1, hw1, hw2]


theorem boxGraph_adj_boxVertDiagonalPredecessor3
    {n : ℕ} (v : FK.boxVerts 3 n)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hheight : boxVertTransverseHeight3 v ≠ 0)
    (hnotlt :
      ¬ ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3))) :
    (FK.boxGraph 3 n).Adj
      (boxVertDiagonalPredecessor3 v hvwedge hheight hnotlt) v := by
  change (hypercubicLattice 3).Adj
    ((boxVertDiagonalPredecessor3 v hvwedge hheight hnotlt :
      FK.boxVerts 3 n) : Lattice.Site 3) (v : Lattice.Site 3)
  rw [hypercubicLattice_adj, Fin.sum_univ_three]
  rcases boxVertDiagonalPredecessor3_hasCoords v hvwedge hheight hnotlt with
    ⟨hw0, hw1, hw2⟩
  simp [hw0, hvwedge.1, hw1, hw2]


theorem boxGraph_adj_boxVertInclLE_strictSectorPredecessor3
    {n M : ℕ} (h : n ≤ M) (v : FK.boxVerts 3 n)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3))) :
    (FK.boxGraph 3 M).Adj
      (FK.boxVertInclLE 3 h
        (boxVertStrictSectorPredecessor3 v hvwedge hlt))
      (FK.boxVertInclLE 3 h v) := by
  simpa [FK.boxGraph, FK.boxVertInclLE] using
    boxGraph_adj_boxVertStrictSectorPredecessor3 v hvwedge hlt


theorem boxGraph_adj_boxVertInclLE_strictSectorYPredecessor3
    {n M : ℕ} (h : n ≤ M) (v : FK.boxVerts 3 n)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) :
    (FK.boxGraph 3 M).Adj
      (FK.boxVertInclLE 3 h
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
      (FK.boxVertInclLE 3 h v) := by
  simpa [FK.boxGraph, FK.boxVertInclLE] using
    boxGraph_adj_boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos


theorem boxGraph_adj_boxVertInclLE_diagonalPredecessor3
    {n M : ℕ} (h : n ≤ M) (v : FK.boxVerts 3 n)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hheight : boxVertTransverseHeight3 v ≠ 0)
    (hnotlt :
      ¬ ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3))) :
    (FK.boxGraph 3 M).Adj
      (FK.boxVertInclLE 3 h
        (boxVertDiagonalPredecessor3 v hvwedge hheight hnotlt))
      (FK.boxVertInclLE 3 h v) := by
  simpa [FK.boxGraph, FK.boxVertInclLE] using
    boxGraph_adj_boxVertDiagonalPredecessor3 v hvwedge hheight hnotlt

set_option linter.style.longLine false in


theorem boxVertPositiveXFaceOrderedWedge3_lowerDoubledAdj_hasCoords3_yOrZ
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hwwedge : boxVertPositiveXFaceOrderedWedge3 n w)
    (hheight : boxVertTransverseHeight3 w < boxVertTransverseHeight3 v)
    (hadj :
      (FK.boxGraph 3 (2 * n)).Adj
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)) :
    boxVertHasCoords3 w (n : ℤ)
        (((v : Lattice.Site 3) (1 : Fin 3)) - 1)
        ((v : Lattice.Site 3) (2 : Fin 3)) ∨
      boxVertHasCoords3 w (n : ℤ)
        ((v : Lattice.Site 3) (1 : Fin 3))
        (((v : Lattice.Site 3) (2 : Fin 3)) - 1) := by
  let y : ℤ := (v : Lattice.Site 3) (1 : Fin 3)
  let z : ℤ := (v : Lattice.Site 3) (2 : Fin 3)
  let yw : ℤ := (w : Lattice.Site 3) (1 : Fin 3)
  let zw : ℤ := (w : Lattice.Site 3) (2 : Fin 3)
  have hy_nonneg : 0 ≤ y := by
    simpa [y] using hvwedge.2.1
  have hz_nonneg : 0 ≤ z := by
    have hy_le_z : y ≤ z := by
      simpa [y, z] using hvwedge.2.2
    omega
  have hyw_nonneg : 0 ≤ yw := by
    simpa [yw] using hwwedge.2.1
  have hzw_nonneg : 0 ≤ zw := by
    have hyw_le_zw : yw ≤ zw := by
      simpa [yw, zw] using hwwedge.2.2
    omega
  have hheight_int : yw + zw < y + z := by
    have hheight_nat :
        yw.natAbs + zw.natAbs < y.natAbs + z.natAbs := by
      simpa [boxVertTransverseHeight3, y, z, yw, zw] using hheight
    have hheight_cast :
        (yw.natAbs : ℤ) + (zw.natAbs : ℤ) <
          (y.natAbs : ℤ) + (z.natAbs : ℤ) := by
      exact_mod_cast hheight_nat
    simpa [
      Int.natAbs_of_nonneg hyw_nonneg,
      Int.natAbs_of_nonneg hzw_nonneg,
      Int.natAbs_of_nonneg hy_nonneg,
      Int.natAbs_of_nonneg hz_nonneg] using hheight_cast
  have hadj_sum :
      (yw - y).natAbs + (zw - z).natAbs = 1 := by
    have hadj_lat :
        (hypercubicLattice 3).Adj
          (w : Lattice.Site 3) (v : Lattice.Site 3) := by
      simpa [FK.boxGraph, FK.boxVertInclLE] using hadj
    rw [hypercubicLattice_adj, Fin.sum_univ_three] at hadj_lat
    simpa [y, z, yw, zw, hvwedge.1, hwwedge.1] using hadj_lat
  have hcases :
      ((yw - y).natAbs = 1 ∧ (zw - z).natAbs = 0) ∨
        ((yw - y).natAbs = 0 ∧ (zw - z).natAbs = 1) := by
    omega
  rcases hcases with hY | hZ
  · rcases hY with ⟨hy_step, hz_zero⟩
    have hzw_eq : zw = z := by
      have : zw - z = 0 := Int.natAbs_eq_zero.mp hz_zero
      omega
    have hy_pm : yw - y = 1 ∨ yw - y = -1 :=
      (Int.natAbs_eq_iff.mp hy_step)
    rcases hy_pm with hy_plus | hy_minus
    · have : ¬ yw + zw < y + z := by
        omega
      exact (this hheight_int).elim
    · left
      refine ⟨hwwedge.1, ?_, ?_⟩ <;> omega
  · rcases hZ with ⟨hy_zero, hz_step⟩
    have hyw_eq : yw = y := by
      have : yw - y = 0 := Int.natAbs_eq_zero.mp hy_zero
      omega
    have hz_pm : zw - z = 1 ∨ zw - z = -1 :=
      (Int.natAbs_eq_iff.mp hz_step)
    rcases hz_pm with hz_plus | hz_minus
    · have : ¬ yw + zw < y + z := by
        omega
      exact (this hheight_int).elim
    · right
      refine ⟨hwwedge.1, ?_, ?_⟩ <;> omega

end Exact3D
end StatMech
