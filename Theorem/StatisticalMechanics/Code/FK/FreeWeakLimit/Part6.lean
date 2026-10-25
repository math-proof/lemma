/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.InducedBC.Part11
import Theorem.StatisticalMechanics.Code.FK.WiredDomChain.Part4
import Theorem.StatisticalMechanics.Code.FK.Limits
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.Foundations.MonotoneLimit
import Theorem.StatisticalMechanics.Code.Foundations.WeakConvergence
import Def.StatisticalMechanics.Code.FK.FreeWeakLimit.Part6
open MeasureTheory Filter Topology SimpleGraph
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK

variable {d : ℕ}


theorem numClusters_psiExt_free (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) :
    numClusters (boxGraph d (n+1)) (psiExt d n ψ ω)
      = numClustersBC (boxGraph d n) (inducedWiringFree d n ψ) ω + outsideShiftFree d n ψ := by
  have hfull : numClusters (boxGraph d (n+1)) (psiExt d n ψ ω)
      = Nat.card (fullGraphFree d n ω ψ).ConnectedComponent := by
    rw [← numClustersBC_bot, numClustersBC, sup_bot_eq, psiFreeGraph_eq_sup]
  have hinner : numClustersBC (boxGraph d n) (inducedWiringFree d n ψ) ω
      = Nat.card (innerGraphFree d n ω ψ).ConnectedComponent := by
    rw [numClustersBC]
  rw [hfull, hinner, outsideShiftFree,
    ← Nat.card_congr (fullComponentEquivFree d n ω ψ), Nat.card_sum]


end FK
end StatMech
