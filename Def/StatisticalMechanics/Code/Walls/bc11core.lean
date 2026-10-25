/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc11core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc9core
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationExistence.Part4
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationExistence2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.BoxMergeFreeMenger.Part2
import Theorem.StatisticalMechanics.Code.Percolation.CanonicalTrifCount.Part4
import Theorem.StatisticalMechanics.Code.Percolation.LatticeMengerAttach.Part4
import Theorem.StatisticalMechanics.Code.Walls.bc7distinctwitnessclusters.Part2
open Set SimpleGraph
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths
open MeasureTheory


namespace StatMech

namespace Walls

variable {d : ℕ}


def bc11_BoxOriginOpenReach (d n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n, ∃ W : Finset (Sym2 (Site d)),
    (∀ e ∈ W, (0 : Site d) ∉ e) ∧
    ∃ y₁ y₂ y₃ : Site d, ∃ R₁ R₂ R₃ : Set (Site d),
      y₁ ≠ 0 ∧ y₂ ≠ 0 ∧ y₃ ≠ 0 ∧
      Connected d (forceOpenFinset W ω) 0 y₁ ∧
      Connected d (forceOpenFinset W ω) 0 y₂ ∧
      Connected d (forceOpenFinset W ω) 0 y₃ ∧
      (cluster d (removeSite 0 ω) y₁).Infinite ∧
      (cluster d (removeSite 0 ω) y₂).Infinite ∧
      (cluster d (removeSite 0 ω) y₃).Infinite ∧
      (y₁ ∈ R₁ ∧ y₂ ∈ R₂ ∧ y₃ ∈ R₃) ∧
      ((∀ u v, u ∈ R₁ → IsOpenEdge d ω u v → v ∈ R₁) ∧
        (∀ u v, u ∈ R₂ → IsOpenEdge d ω u v → v ∈ R₂) ∧
        (∀ u v, u ∈ R₃ → IsOpenEdge d ω u v → v ∈ R₃)) ∧
      ((∀ u v, u ∈ R₁ → s(u, v) ∈ W → v ∈ R₁) ∧
        (∀ u v, u ∈ R₂ → s(u, v) ∈ W → v ∈ R₂) ∧
        (∀ u v, u ∈ R₃ → s(u, v) ∈ W → v ∈ R₃)) ∧
      (Disjoint R₁ R₂ ∧ Disjoint R₁ R₃ ∧ Disjoint R₂ R₃)


end Walls
end StatMech
