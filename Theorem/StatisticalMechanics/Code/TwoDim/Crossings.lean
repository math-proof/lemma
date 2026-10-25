/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/Crossings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.TwoDim.Crossings
open Set


namespace StatMech

namespace TwoDim

open StatMech.Lattice

variable {a b : ℤ}


@[simp]
theorem mem_rectangle {x : Site 2} :
    x ∈ rectangle a b ↔ 0 ≤ x 0 ∧ x 0 ≤ a ∧ 0 ≤ x 1 ∧ x 1 ≤ b := Iff.rfl


theorem rectangle_finite (a b : ℤ) : (rectangle a b).Finite := by
  apply Set.Finite.subset
    (Set.Finite.pi (fun _ : Fin 2 => Set.finite_Icc (0 : ℤ) (max a b)))
  intro x hx i _
  fin_cases i
  · simpa only [Set.mem_Icc] using ⟨hx.1, le_trans hx.2.1 (le_max_left a b)⟩
  · simpa only [Set.mem_Icc] using ⟨hx.2.2.1, le_trans hx.2.2.2 (le_max_right a b)⟩


end TwoDim
end StatMech
