/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Defs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.TwoDim.Crossings.Part4
import Def.StatisticalMechanics.Code.RSW.Defs
open Set


namespace StatMech

namespace RSW

namespace Box

open StatMech.Lattice

open StatMech.TwoDim


@[simp]
theorem mem_rect {a b c d : ℤ} {x : Site 2} :
    x ∈ rect a b c d ↔ a ≤ x 0 ∧ x 0 ≤ b ∧ c ≤ x 1 ∧ x 1 ≤ d := Iff.rfl


theorem rect_finite (a b c d : ℤ) : (rect a b c d).Finite := by
  apply Set.Finite.subset
    (Set.Finite.pi (fun i : Fin 2 => Set.finite_Icc (![a, c] i) (![b, d] i)))
  intro x hx i _
  fin_cases i
  · simpa only [Matrix.cons_val_zero, Set.mem_Icc] using ⟨hx.1, hx.2.1⟩
  · simpa only [Matrix.cons_val_one, Matrix.head_cons, Set.mem_Icc] using ⟨hx.2.2.1, hx.2.2.2⟩


end Box
end RSW
end StatMech
