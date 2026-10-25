/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean -/

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
import Theorem.StatisticalMechanics.Code.FK.BoxCrossGraph.Part19
import Theorem.StatisticalMechanics.Code.FK.IvProperties
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
import Def.StatisticalMechanics.Code.FK.InducedBC.Part10
open scoped BigOperators
open SimpleGraph

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

open StatMech.Lattice

variable {d : ℕ}


theorem numClustersBC_psiExt (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) :
    numClustersBC (boxGraph d (n+1))
        (StatMech.Lattice.boundaryCliqueGraph (boxBoundary d (n+1))) (psiExt d n ψ ω)
      = numClustersBC (boxGraph d n) (inducedWiring d n ψ) ω + outsideShift d n ψ := by
  have hfull : numClustersBC (boxGraph d (n+1))
        (StatMech.Lattice.boundaryCliqueGraph (boxBoundary d (n+1))) (psiExt d n ψ ω)
      = Nat.card (fullGraph d n ω ψ).ConnectedComponent := by
    rw [numClustersBC, psiWiredGraph_eq_sup]
  have hinner : numClustersBC (boxGraph d n) (inducedWiring d n ψ) ω
      = Nat.card (innerGraph d n ω ψ).ConnectedComponent := by
    rw [numClustersBC]
  rw [hfull, hinner, outsideShift,
    ← Nat.card_congr (fullComponentEquiv d n ω ψ), Nat.card_sum]


end FK
end StatMech
