/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Def.StatisticalMechanics.Code.FK.ContinuousRectangleCrossing.Part4
open Set SimpleGraph Topology
open scoped unitInterval


namespace StatMech

namespace ContinuousRectangleCrossing

open Lattice RSW.Box


@[simp] theorem sampleTime_zero (N : ℕ) (hN : 0 < N) :
    sampleTime N 0 (Nat.zero_le N) hN = 0 := by
  ext
  simp [sampleTime]

@[simp] theorem sampleTime_self (N : ℕ) (hN : 0 < N) :
    sampleTime N N (le_refl N) hN = 1 := by
  ext
  simp [sampleTime, hN.ne']

theorem dist_sampleTime_succ (N k : ℕ) (hk : k < N) (hN : 0 < N) :
    dist (sampleTime N k hk.le hN)
        (sampleTime N (k + 1) (Nat.succ_le_iff.2 hk) hN) = 1 / (N : ℝ) := by
  rw [Subtype.dist_eq, Real.dist_eq]
  simp only [sampleTime]
  rw [abs_of_nonpos]
  · have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp
    push_cast
    ring
  · have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    rw [sub_nonpos, div_le_div_iff_of_pos_right hNr]
    exact_mod_cast Nat.le_succ k


end ContinuousRectangleCrossing
end StatMech
