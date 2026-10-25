/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWGapSymmetry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part101
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

@[simp] theorem rlc_flipX_mem_image_iff (P : Finset (Site 2))
    (z : Site 2) :
    rlc_flipX z ∈ P.image rlc_flipX ↔ z ∈ P := by
  classical
  constructor
  · intro hz
    obtain ⟨w, hw, hzw⟩ := Finset.mem_image.mp hz
    have hwz : w = z := rlc_flipX.injective hzw
    simpa [hwz] using hw
  · intro hz
    exact Finset.mem_image.mpr ⟨z, hz, rfl⟩

@[simp] theorem rlc_mem_flipX_image_iff (P : Finset (Site 2))
    (z : Site 2) :
    z ∈ P.image rlc_flipX ↔ rlc_flipX z ∈ P := by
  simpa using rlc_flipX_mem_image_iff P (rlc_flipX z)

theorem rlc_connectorBarrier_mem_flipX_iff {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (z : Site 2) :
    z ∈ rlc_connectorBarrier gamma gamma' ↔
      rlc_flipX z ∈ rlc_connectorBarrier gamma gamma' := by
  classical
  simp only [rlc_connectorBarrier, Finset.mem_union,
    rlc_mem_flipX_image_iff, rlc_flipX_involutive]
  tauto

theorem rlc_connectorBox_mem_flipX_iff {n : ℤ} (z : Site 2) :
    z ∈ rlc_connectorBox n ↔ rlc_flipX z ∈ rlc_connectorBox n := by
  simpa [rlc_connectorBox] using rlc_mem_connectorBox_flipX (n := n) z

theorem rlc_connectorAllowed_mem_flipX_iff {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (z : Site 2) :
    z ∈ rlc_connectorAllowed gamma gamma' ↔
      rlc_flipX z ∈ rlc_connectorAllowed gamma gamma' := by
  simp only [rlc_connectorAllowed, Finset.mem_sdiff]
  rw [
    rlc_connectorBox_mem_flipX_iff,
    rlc_connectorBarrier_mem_flipX_iff]

theorem rlc_adj_flipX (x y : Site 2) :
    (hypercubicLattice 2).Adj x y ↔
      (hypercubicLattice 2).Adj (rlc_flipX x) (rlc_flipX y) := by
  rw [hypercubicLattice_adj, hypercubicLattice_adj,
    Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [rlc_flipX, rlc_flipXFun, Equiv.coe_fn_mk,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show (-x 0) - (-y 0) = -(x 0 - y 0) by ring, Int.natAbs_neg]

end Universality
end StatMech
