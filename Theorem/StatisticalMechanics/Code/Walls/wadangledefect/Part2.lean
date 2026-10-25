/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wadangledefect.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.euceuler.Part3
import Def.StatisticalMechanics.Code.Walls.wadangledefect.Part2
open scoped BigOperators
open Finset
open StatMech.Euc


namespace StatMech.Wad

theorem wad_defect_eq_four_chi (K : Finset Cell) :
    ∑ v ∈ regVerts K, defect K v = 4 * regChi K := by
  classical
  have hexpand : ∑ v ∈ regVerts K, defect K v
      = 4 * ((regVerts K).card : ℤ)
        - 2 * (∑ v ∈ regVerts K, (edgeDeg K v : ℤ))
        + (∑ v ∈ regVerts K, (cellDeg K v : ℤ)) := by
    unfold defect
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum]
    ring
  rw [hexpand]
  have hA : (∑ v ∈ regVerts K, (cellDeg K v : ℤ)) = 4 * (K.card : ℤ) := by
    rw [← Nat.cast_sum, wad_angleSum]; push_cast; ring
  have hB : (∑ v ∈ regVerts K, (edgeDeg K v : ℤ)) = 2 * ((regEdges K).card : ℤ) := by
    rw [← Nat.cast_sum, wad_edgeSum]; push_cast; ring
  rw [hA, hB]
  unfold regChi
  ring


end StatMech.Wad
