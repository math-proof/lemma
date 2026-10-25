/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BoundaryPruningClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.ForestLeafCountClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SingleLeafHallClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BoundaryPruningClose
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


open Classical in


def bpr_TreeForestData (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (G : SimpleGraph W) (_ : DecidableRel G.Adj)
    (π : W → Site d) (ιT : Site d → W) (br : Site d → Fin 3 → W) (lamL : W → Site d),
    G.IsTree ∧ 2 ≤ Fintype.card W ∧
    (∀ u v, G.Adj u v → (openSubgraph d ω).Adj (π u) (π v)) ∧
    Function.Injective π ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → π (ιT x) = x) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      ιT x = ιT y → x = y) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      (∀ i, Connected d ω x (π (br x i)) ∧ br x i ≠ ιT x ∧ G.Reachable (ιT x) (br x i)) ∧
      (π (br x 0) ≠ π (br x 1) ∧ π (br x 0) ≠ π (br x 2) ∧ π (br x 1) ≠ π (br x 2)) ∧
      (¬ Connected d (removeSite x ω) (π (br x 0)) (π (br x 1)) ∧
       ¬ Connected d (removeSite x ω) (π (br x 0)) (π (br x 2)) ∧
       ¬ Connected d (removeSite x ω) (π (br x 1)) (π (br x 2)))) ∧
    (∀ v, G.degree v = 1 → lamL v ∈ vertexBoundary d n) ∧
    Set.InjOn lamL (univ.filter (fun v => G.degree v = 1))


end Percolation
end StatMech
