/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OutwardArmForestClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve.Part5
import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeArmClose.Part3
import Theorem.StatisticalMechanics.Code.Percolation.BKForestLib.Part6
import Theorem.StatisticalMechanics.Code.Percolation.ForestLeafDisjointClose.Part2
import Def.StatisticalMechanics.Code.Percolation.OutwardArmForestClose.Part2
open Set SimpleGraph Finset
open scoped BigOperators

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem oaf_abstractForestPeel_false_of_rootCover {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (T : Finset V) {r : V} {c : Fin 3 → V}
    (hrT : r ∈ T) (hcT : ∀ i, c i ∈ T) (hcne : ∀ i, c i ≠ r)
    (hcover : ∀ a, G.Reachable r a → a ∉ T → ∃ i, (oaf_cutGraph G r).Reachable a (c i)) :
    ¬ oaf_AbstractForestPeel G T := by
  intro h
  obtain ⟨a, hra, haT, hpriv⟩ := h r hrT
  obtain ⟨i, hai⟩ := hcover a hra haT
  exact hpriv (c i) (hcT i) (hcne i) hai


theorem oaf_reach_eqLabel {V L : Type*} (H : SimpleGraph V) (φ : V → L)
    (hφ : ∀ a b, H.Adj a b → φ a = φ b) {x y : V} (h : H.Reachable x y) : φ x = φ y := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => rfl
  | cons hadj _ ih => exact (hφ _ _ hadj).trans ih


end Percolation
end StatMech
