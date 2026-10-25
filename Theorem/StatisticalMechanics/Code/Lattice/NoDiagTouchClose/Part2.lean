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
import Def.StatisticalMechanics.Code.Lattice.NoDiagTouchClose.Part2
open SimpleGraph Function Set


namespace StatMech

namespace Lattice

theorem ndt_kingSaturated_sublevel (φ ψ : ℤ → ℤ) (c : ℤ) :
    npm_KingSaturated (ndt_sublevel φ ψ c) := by
  intro f
  simp only [ndt_sublevel, Set.mem_setOf_eq, npd_P00, npd_P11, npd_P10, npd_P01,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  refine ⟨fun h00 h11 => ?_, fun h10 h01 => ?_⟩
  · by_cases hh : φ (f 0 + 1) + ψ (f 1) ≤ c
    · exact Or.inl hh
    · exact Or.inr (by omega)
  · by_cases hh : φ (f 0) + ψ (f 1) ≤ c
    · exact Or.inl hh
    · exact Or.inr (by omega)


end Lattice
end StatMech
