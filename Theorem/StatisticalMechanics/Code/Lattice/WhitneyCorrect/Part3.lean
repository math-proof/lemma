/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyCorrect.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanBridgeCycle.Part10
import Def.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part2
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem whc_dualCross_parity (H : SimpleGraph (Site 2)) (φ : Site 2 → Prop)
    (hcompat : whc_CompatColoring H φ) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) :
    Even (whc_dualCross H w) ↔ (φ x ↔ φ y) := by
  classical
  induction w with
  | nil => simp [whc_dualCross]
  | @cons a b c hab p ih =>
    rw [whc_dualCross_cons H hab p]
    by_cases hcr : whc_isCross H a b
    · rw [if_pos hcr, add_comm, Nat.even_add_one, ih]
      have := (hcompat a b hab).mp hcr
      by_cases ha : φ a <;> by_cases hb : φ b <;> by_cases hc : φ c <;> simp_all
    · rw [if_neg hcr, zero_add, ih]
      have := (fun hh => hcr ((hcompat a b hab).mpr hh))
      by_cases ha : φ a <;> by_cases hb : φ b <;> by_cases hc : φ c <;> simp_all


end Lattice
end StatMech
