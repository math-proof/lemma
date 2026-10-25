/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.DomainMarkov.Part5
import Theorem.StatisticalMechanics.Code.FK.WiredDominationInner.Part3
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
import Def.StatisticalMechanics.Code.FK.BoxCrossGraph.Part18
open scoped BigOperators
open SimpleGraph

set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.Lattice


theorem numClustersBC_crossExt_add (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    {D : SimpleGraph (boxVerts d (n+1))} [DecidableRel D.Adj]
    (hD : IsAnnulusWiring d n D) :
    numClustersBC (boxGraph d (n+1))
        (StatMech.Lattice.boundaryCliqueGraph (innerBdry d n) ⊔ D) (crossExt d n ω)
      = StatMech.Lattice.numClustersWired (boxGraph d n) (boxBoundary d n) ω
        + Nat.card (annulusSubgraph d n D).ConnectedComponent := by
  rw [numClustersBC, openSub_sup_eq_crossWiredGraphAdd, numClustersWired_eq_card]
  show Nat.card (crossWiredGraphAdd d n ω D).ConnectedComponent
      = Fintype.card (innerWiredGraph d n ω).ConnectedComponent
        + Nat.card (annulusSubgraph d n D).ConnectedComponent
  rw [← Nat.card_eq_fintype_card, ← Nat.card_sum,
    Nat.card_congr (crossComponentEquivAdd d n ω hD).symm]


end FK
end StatMech
