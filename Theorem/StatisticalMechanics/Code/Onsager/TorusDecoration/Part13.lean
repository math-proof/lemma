/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.TrivalentCycles
import Theorem.StatisticalMechanics.Code.Onsager.TurningTelescope.Part3
import Theorem.StatisticalMechanics.Code.Onsager.Torus
import Def.StatisticalMechanics.Code.Onsager.TorusDecoration.Part13


namespace StatMech.Onsager

open Finset SimpleGraph

open StatMech.Ising

theorem ons_decorated_evenSubgraph_cycle_decomposition
    (L : ℕ) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ evenSubgraphs (onsTorusGraph L)) :
    let D := ons_decoratedEdges (ons_evenSubgraphPortPattern L F hF)
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (base : ι → ons_Dart L)
      (p : (i : ι) → (ons_decGraph L).Walk (base i) (base i)),
      (∀ i, (p i).IsCycle) ∧
      D = Finset.univ.biUnion (fun i => (p i).edges.toFinset) ∧
      ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint
        (fun i => (p i).edges.toFinset) := by
  dsimp only
  obtain ⟨ι, hi, hdeci, base, p, hcycle, hcover, hedge, _⟩ :=
    ons_trivalent_even_cycle_decomposition (ons_decGraph L)
      (ons_decGraph_degree_le_three L)
      (ons_decoratedEdges (ons_evenSubgraphPortPattern L F hF))
      (ons_decoratedEdges_even L (ons_evenSubgraphPortPattern L F hF))
  exact ⟨ι, hi, hdeci, base, p, hcycle, hcover, hedge⟩

end StatMech.Onsager
