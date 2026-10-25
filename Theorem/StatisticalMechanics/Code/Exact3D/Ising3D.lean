/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Ising3D.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Exact3D.CorrelationLength.Part3
import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part6
import Theorem.StatisticalMechanics.Code.Ising.InfiniteVolume.Part9
import Def.StatisticalMechanics.Code.Ising.Magnetization.Part3
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Exact3D.Ising3D
open MeasureTheory


namespace StatMech

namespace Exact3D

open StatMech.Lattice


theorem ising3DOrigin_mem_box (n : ℕ) :
    ising3DOrigin ∈ box 3 n := by
  intro i
  simp [ising3DOrigin]


theorem ising3DXAxisRay_mem_box_self (n : ℕ) :
    ising3DXAxisRay n ∈ box 3 n := by
  intro i
  fin_cases i <;> simp [ising3DXAxisRay, ising3DSiteOfCoords]


theorem ising3DXAxisRay_mem_box_le {n N : ℕ} (h : n ≤ N) :
    ising3DXAxisRay n ∈ box 3 N := by
  intro i
  fin_cases i
  · simpa [ising3DXAxisRay, ising3DSiteOfCoords] using h
  · simp [ising3DXAxisRay, ising3DSiteOfCoords]
  · simp [ising3DXAxisRay, ising3DSiteOfCoords]

@[simp] theorem ising3DXAxisRay_zero :
    ising3DXAxisRay 0 = ising3DOrigin := by
  ext i
  fin_cases i <;> rfl

@[simp] theorem ising3DYAxisRay_zero :
    ising3DYAxisRay 0 = ising3DOrigin := by
  ext i
  fin_cases i <;> rfl

@[simp] theorem ising3DZAxisRay_zero :
    ising3DZAxisRay 0 = ising3DOrigin := by
  ext i
  fin_cases i <;> rfl

@[simp] theorem blockRepresentative_ising3DXAxisRay
    (scale : BlockScale) (n : ℕ) :
    blockRepresentative scale (ising3DXAxisRay n) =
      ising3DXAxisRay (scale.L * n) := by
  ext i
  fin_cases i <;>
    simp [blockRepresentative, ising3DXAxisRay, ising3DSiteOfCoords]

@[simp] theorem blockRepresentative_ising3DYAxisRay
    (scale : BlockScale) (n : ℕ) :
    blockRepresentative scale (ising3DYAxisRay n) =
      ising3DYAxisRay (scale.L * n) := by
  ext i
  fin_cases i <;>
    simp [blockRepresentative, ising3DYAxisRay, ising3DSiteOfCoords]

@[simp] theorem blockRepresentative_ising3DZAxisRay
    (scale : BlockScale) (n : ℕ) :
    blockRepresentative scale (ising3DZAxisRay n) =
      ising3DZAxisRay (scale.L * n) := by
  ext i
  fin_cases i <;>
    simp [blockRepresentative, ising3DZAxisRay, ising3DSiteOfCoords]

@[simp] theorem blockIndexOf_ising3DXAxisRay_scale_mul
    (scale : BlockScale) (n : ℕ) :
    blockIndexOf scale (ising3DXAxisRay (scale.L * n)) =
      ising3DXAxisRay n := by
  calc
    blockIndexOf scale (ising3DXAxisRay (scale.L * n)) =
        blockIndexOf scale (blockRepresentative scale (ising3DXAxisRay n)) := by
      rw [blockRepresentative_ising3DXAxisRay]
    _ = ising3DXAxisRay n :=
      blockIndexOf_blockRepresentative scale (ising3DXAxisRay n)

@[simp] theorem blockIndexOf_ising3DYAxisRay_scale_mul
    (scale : BlockScale) (n : ℕ) :
    blockIndexOf scale (ising3DYAxisRay (scale.L * n)) =
      ising3DYAxisRay n := by
  calc
    blockIndexOf scale (ising3DYAxisRay (scale.L * n)) =
        blockIndexOf scale (blockRepresentative scale (ising3DYAxisRay n)) := by
      rw [blockRepresentative_ising3DYAxisRay]
    _ = ising3DYAxisRay n :=
      blockIndexOf_blockRepresentative scale (ising3DYAxisRay n)

@[simp] theorem blockIndexOf_ising3DZAxisRay_scale_mul
    (scale : BlockScale) (n : ℕ) :
    blockIndexOf scale (ising3DZAxisRay (scale.L * n)) =
      ising3DZAxisRay n := by
  calc
    blockIndexOf scale (ising3DZAxisRay (scale.L * n)) =
        blockIndexOf scale (blockRepresentative scale (ising3DZAxisRay n)) := by
      rw [blockRepresentative_ising3DZAxisRay]
    _ = ising3DZAxisRay n :=
      blockIndexOf_blockRepresentative scale (ising3DZAxisRay n)

@[simp] theorem blockRemainder_ising3DXAxisRay_scale_mul
    (scale : BlockScale) (n : ℕ) :
    blockRemainder scale (ising3DXAxisRay (scale.L * n)) =
      ising3DOrigin := by
  calc
    blockRemainder scale (ising3DXAxisRay (scale.L * n)) =
        blockRemainder scale (blockRepresentative scale (ising3DXAxisRay n)) := by
      rw [blockRepresentative_ising3DXAxisRay]
    _ = ising3DOrigin := by
      simpa [ising3DOrigin] using
        blockRemainder_blockRepresentative scale (ising3DXAxisRay n)

@[simp] theorem blockRemainder_ising3DYAxisRay_scale_mul
    (scale : BlockScale) (n : ℕ) :
    blockRemainder scale (ising3DYAxisRay (scale.L * n)) =
      ising3DOrigin := by
  calc
    blockRemainder scale (ising3DYAxisRay (scale.L * n)) =
        blockRemainder scale (blockRepresentative scale (ising3DYAxisRay n)) := by
      rw [blockRepresentative_ising3DYAxisRay]
    _ = ising3DOrigin := by
      simpa [ising3DOrigin] using
        blockRemainder_blockRepresentative scale (ising3DYAxisRay n)

@[simp] theorem blockRemainder_ising3DZAxisRay_scale_mul
    (scale : BlockScale) (n : ℕ) :
    blockRemainder scale (ising3DZAxisRay (scale.L * n)) =
      ising3DOrigin := by
  calc
    blockRemainder scale (ising3DZAxisRay (scale.L * n)) =
        blockRemainder scale (blockRepresentative scale (ising3DZAxisRay n)) := by
      rw [blockRepresentative_ising3DZAxisRay]
    _ = ising3DOrigin := by
      simpa [ising3DOrigin] using
        blockRemainder_blockRepresentative scale (ising3DZAxisRay n)


end Exact3D
end StatMech
