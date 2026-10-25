/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteIsingFKBridge.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.SurfaceTensionConvexity
import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
import Theorem.StatisticalMechanics.Code.FK.RotationInvariance.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.IsingBoxEncoding.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneProps.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.SimonLiebFull.Part2
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part108
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

@[simp] theorem boxVertDiagonalPredecessor3_hasCoords
    {n : ℕ} (v : FK.boxVerts 3 n)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hheight : boxVertTransverseHeight3 v ≠ 0)
    (hnotlt :
      ¬ ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3))) :
    boxVertHasCoords3
      (boxVertDiagonalPredecessor3 v hvwedge hheight hnotlt)
      (n : ℤ)
      (((v : Lattice.Site 3) (1 : Fin 3)) - 1)
      ((v : Lattice.Site 3) (2 : Fin 3)) := by
  simp [boxVertDiagonalPredecessor3, boxVertOfCoords3, boxVertHasCoords3,
    ising3DSiteOfCoords]


theorem exists_boxVertHasCoords3_orderedWedge_diagonal_predY
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hheight : boxVertTransverseHeight3 v ≠ 0)
    (hnotlt :
      ¬ ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3))) :
    ∃ w : FK.boxVerts 3 n,
      boxVertHasCoords3 w
        (n : ℤ)
        (((v : Lattice.Site 3) (1 : Fin 3)) - 1)
        ((v : Lattice.Site 3) (2 : Fin 3)) :=
  ⟨boxVertDiagonalPredecessor3 v hvwedge hheight hnotlt, by simp⟩


theorem boxVertStrictSectorPredecessor3_wedge
    {n : ℕ} (v : FK.boxVerts 3 n)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3))) :
    boxVertPositiveXFaceOrderedWedge3 n
      (boxVertStrictSectorPredecessor3 v hvwedge hlt) := by
  rcases boxVertStrictSectorPredecessor3_hasCoords v hvwedge hlt with
    ⟨hw0, hw1, hw2⟩
  refine ⟨hw0, ?_, ?_⟩
  · rw [hw1]
    exact hvwedge.2.1
  · rw [hw1, hw2]
    omega


theorem boxVertStrictSectorPredecessor3_height_lt
    {n : ℕ} (v : FK.boxVerts 3 n)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3))) :
    boxVertTransverseHeight3
        (boxVertStrictSectorPredecessor3 v hvwedge hlt) <
      boxVertTransverseHeight3 v := by
  let y : ℤ := (v : Lattice.Site 3) (1 : Fin 3)
  let z : ℤ := (v : Lattice.Site 3) (2 : Fin 3)
  rcases boxVertStrictSectorPredecessor3_hasCoords v hvwedge hlt with
    ⟨_hw0, hw1, hw2⟩
  have hz_minus_nonneg : 0 ≤ z - 1 := by
    have hy_nonneg : 0 ≤ y := by
      simpa [y] using hvwedge.2.1
    omega
  have hzm_lt_z : (z - 1).natAbs < z.natAbs :=
    Int.natAbs_lt_natAbs_of_nonneg_of_lt hz_minus_nonneg (by omega)
  calc
    boxVertTransverseHeight3
        (boxVertStrictSectorPredecessor3 v hvwedge hlt) =
        y.natAbs + (z - 1).natAbs := by
          simp [boxVertTransverseHeight3, y, z, hw1, hw2]
    _ < y.natAbs + z.natAbs := Nat.add_lt_add_left hzm_lt_z _
    _ = boxVertTransverseHeight3 v := by
      simp [boxVertTransverseHeight3, y, z]


theorem boxVertStrictSectorYPredecessor3_wedge
    {n : ℕ} (v : FK.boxVerts 3 n)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) :
    boxVertPositiveXFaceOrderedWedge3 n
      (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) := by
  let y : ℤ := (v : Lattice.Site 3) (1 : Fin 3)
  let z : ℤ := (v : Lattice.Site 3) (2 : Fin 3)
  rcases boxVertStrictSectorYPredecessor3_hasCoords
    v hvwedge hlt hypos with
    ⟨hw0, hw1, hw2⟩
  refine ⟨hw0, ?_, ?_⟩
  · rw [hw1]
    omega
  · rw [hw1, hw2]
    omega


theorem boxVertStrictSectorYPredecessor3_height_lt
    {n : ℕ} (v : FK.boxVerts 3 n)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) :
    boxVertTransverseHeight3
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) <
      boxVertTransverseHeight3 v := by
  let y : ℤ := (v : Lattice.Site 3) (1 : Fin 3)
  let z : ℤ := (v : Lattice.Site 3) (2 : Fin 3)
  rcases boxVertStrictSectorYPredecessor3_hasCoords
    v hvwedge hlt hypos with
    ⟨_hw0, hw1, hw2⟩
  have hy_minus_nonneg : 0 ≤ y - 1 := by
    omega
  have hym_lt_y : (y - 1).natAbs < y.natAbs :=
    Int.natAbs_lt_natAbs_of_nonneg_of_lt hy_minus_nonneg (by omega)
  calc
    boxVertTransverseHeight3
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) =
        (y - 1).natAbs + z.natAbs := by
          simp [boxVertTransverseHeight3, y, z, hw1, hw2]
    _ < y.natAbs + z.natAbs := Nat.add_lt_add_right hym_lt_y _
    _ = boxVertTransverseHeight3 v := by
      simp [boxVertTransverseHeight3, y, z]


theorem boxVertDiagonalPredecessor3_wedge
    {n : ℕ} (v : FK.boxVerts 3 n)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hheight : boxVertTransverseHeight3 v ≠ 0)
    (hnotlt :
      ¬ ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3))) :
    boxVertPositiveXFaceOrderedWedge3 n
      (boxVertDiagonalPredecessor3 v hvwedge hheight hnotlt) := by
  let y : ℤ := (v : Lattice.Site 3) (1 : Fin 3)
  let z : ℤ := (v : Lattice.Site 3) (2 : Fin 3)
  rcases boxVertDiagonalPredecessor3_hasCoords v hvwedge hheight hnotlt with
    ⟨hw0, hw1, hw2⟩
  have hy_le_z : y ≤ z := by
    simpa [y, z] using hvwedge.2.2
  have hy_ne_zero : y ≠ 0 := by
    intro hy0
    have hz0 : z = 0 := by omega
    apply hheight
    simp [boxVertTransverseHeight3, y, z, hy0, hz0]
  have hy_pos : 0 < y := by
    have hy_nonneg : 0 ≤ y := by
      simpa [y] using hvwedge.2.1
    omega
  refine ⟨hw0, ?_, ?_⟩
  · rw [hw1]
    omega
  · rw [hw1, hw2]
    omega


theorem boxVertDiagonalPredecessor3_height_lt
    {n : ℕ} (v : FK.boxVerts 3 n)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hheight : boxVertTransverseHeight3 v ≠ 0)
    (hnotlt :
      ¬ ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3))) :
    boxVertTransverseHeight3
        (boxVertDiagonalPredecessor3 v hvwedge hheight hnotlt) <
      boxVertTransverseHeight3 v := by
  let y : ℤ := (v : Lattice.Site 3) (1 : Fin 3)
  let z : ℤ := (v : Lattice.Site 3) (2 : Fin 3)
  rcases boxVertDiagonalPredecessor3_hasCoords v hvwedge hheight hnotlt with
    ⟨_hw0, hw1, hw2⟩
  have hy_le_z : y ≤ z := by
    simpa [y, z] using hvwedge.2.2
  have hy_ne_zero : y ≠ 0 := by
    intro hy0
    have hz0 : z = 0 := by omega
    apply hheight
    simp [boxVertTransverseHeight3, y, z, hy0, hz0]
  have hy_pos : 0 < y := by
    have hy_nonneg : 0 ≤ y := by
      simpa [y] using hvwedge.2.1
    omega
  have hy_minus_nonneg : 0 ≤ y - 1 := by
    omega
  have hym_lt_y : (y - 1).natAbs < y.natAbs :=
    Int.natAbs_lt_natAbs_of_nonneg_of_lt hy_minus_nonneg (by omega)
  calc
    boxVertTransverseHeight3
        (boxVertDiagonalPredecessor3 v hvwedge hheight hnotlt) =
        (y - 1).natAbs + z.natAbs := by
          simp [boxVertTransverseHeight3, y, z, hw1, hw2]
    _ < y.natAbs + z.natAbs := Nat.add_lt_add_right hym_lt_y _
    _ = boxVertTransverseHeight3 v := by
      simp [boxVertTransverseHeight3, y, z]


end Exact3D
end StatMech
