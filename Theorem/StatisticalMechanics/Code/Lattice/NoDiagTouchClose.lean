/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoDiagTouchClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.Umlaufsatz.Part4
import Theorem.StatisticalMechanics.Code.Lattice.UmlaufsatzSingleCycle.Part4
import Theorem.StatisticalMechanics.Code.Lattice.NoPinchDual.Part4
import Theorem.StatisticalMechanics.Code.Lattice.NoPinchMatching.Part2
import Theorem.StatisticalMechanics.Code.Lattice.Wall1EmbeddingRetry
import Def.StatisticalMechanics.Code.Lattice.NoDiagTouchClose
open SimpleGraph Function Set


namespace StatMech

namespace Lattice

theorem ndt_kingSaturated_product (A B : Set ℤ) : npm_KingSaturated (ndt_product A B) := by
  intro f
  simp only [ndt_product, Set.mem_setOf_eq, npd_P00, npd_P11, npd_P10, npd_P01,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  exact ⟨fun h00 h11 => Or.inl ⟨h11.1, h00.2⟩, fun h10 h01 => Or.inl ⟨h01.1, h10.2⟩⟩


theorem ndt_box_eq_product (n : ℕ) :
    box 2 n = ndt_product {t : ℤ | t.natAbs ≤ n} {t : ℤ | t.natAbs ≤ n} := by
  ext x
  simp only [box, ndt_product, Set.mem_setOf_eq]
  refine ⟨fun h => ⟨h 0, h 1⟩, fun ⟨h0, h1⟩ i => ?_⟩
  fin_cases i
  · exact h0
  · exact h1


theorem ndt_kingSaturated_box (n : ℕ) : npm_KingSaturated (box 2 n) := by
  rw [ndt_box_eq_product]; exact ndt_kingSaturated_product _ _


end Lattice
end StatMech
