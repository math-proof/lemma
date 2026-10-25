/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SubcriticalDecay.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Theta
import Def.StatisticalMechanics.Code.Percolation.TildePc.Part4
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Percolation.SubcriticalDecay
open MeasureTheory Set
open scoped NNReal ENNReal


namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}


@[simp]
theorem mem_crossingEvent {n : ℕ} {ω : ConfigSpace (Sym2 (Site d))} :
    ω ∈ crossingEvent d n ↔ ∃ v, Connected d ω (origin d) v ∧ v ∉ box d (n - 1) :=
  Iff.rfl


theorem crossingEvent_antitone (m n : ℕ) (hmn : m ≤ n) :
    crossingEvent d n ⊆ crossingEvent d m := by
  intro ω hω
  obtain ⟨v, hconn, hv⟩ := hω
  exact ⟨v, hconn, fun hvm => hv (box_mono d (by omega) hvm)⟩


end Percolation
end StatMech
