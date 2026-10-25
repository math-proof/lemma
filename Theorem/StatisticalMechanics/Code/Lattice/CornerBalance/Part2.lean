/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
import Def.StatisticalMechanics.Code.Lattice.CornerBalance.Part2
open SimpleGraph Function


namespace StatMech

namespace Lattice

theorem unitCell_finite : unitCell.Finite := Set.finite_singleton _


theorem origin_mem_unitCell : (![0, 0] : Site 2) ∈ unitCell := rfl


theorem not_mem_unitCell (v : Site 2) (h : v 0 ≠ 0 ∨ v 1 ≠ 0) : v ∉ unitCell := by
  simp only [unitCell, Set.mem_singleton_iff]
  intro hv
  rcases h with h | h
  · exact h (by rw [hv]; simp)
  · exact h (by rw [hv]; simp)


theorem unitWt_px : unitWt (![1, 0] : Site 2) = 1 := by simp [unitWt, Fin.sum_univ_two]

theorem unitWt_my : unitWt (![0, -1] : Site 2) = 1 := by simp [unitWt, Fin.sum_univ_two]

theorem unitWt_mx : unitWt (![-1, 0] : Site 2) = 1 := by simp [unitWt, Fin.sum_univ_two]

theorem unitWt_py : unitWt (![0, 1] : Site 2) = 1 := by simp [unitWt, Fin.sum_univ_two]


end Lattice
end StatMech
