/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OpenSpanningForestClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.BoundaryPruningClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BKSpanningTreeClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.OpenSpanningForestClose
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


open Classical in


def osf_PeeledBoxForest (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ (Vset : Finset (Site d)) (_ : Nonempty (↑Vset : Type)) (F₀ : SimpleGraph (↑Vset : Type))
    (vx : Site d → (↑Vset : Type)) (b : Site d → Fin 3 → (↑Vset : Type)),
    (∀ u v, F₀.Adj u v → (openSubgraph d ω).Adj (u : Site d) (v : Site d)) ∧
    (∀ v : (↑Vset : Type), 1 ≤ (osf_spanForest F₀).degree v) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      ((vx x : Site d) = x ∧
       (∀ i, F₀.Reachable (vx x) (b x i) ∧ b x i ≠ vx x) ∧
       (¬ Connected d (removeSite x ω) (b x 0 : Site d) (b x 1 : Site d) ∧
        ¬ Connected d (removeSite x ω) (b x 0 : Site d) (b x 2 : Site d) ∧
        ¬ Connected d (removeSite x ω) (b x 1 : Site d) (b x 2 : Site d)))) ∧
    (∀ v : (↑Vset : Type), (osf_spanForest F₀).degree v = 1 → (v : Site d) ∈ vertexBoundary d n)


end Percolation
end StatMech
