/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusEmbedding.Part3
import Theorem.StatisticalMechanics.Code.Ising.GinibreBoundary
import Theorem.StatisticalMechanics.Code.Ising.GHSVertexPartition.Part8
import Theorem.StatisticalMechanics.Code.Sharpness.HighTempPlusBox.Part5
import Theorem.StatisticalMechanics.Code.FrontierB.InhomogeneousFiniteVolumeRelabel.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsingTorusFreeBoundaryComparison.Part7
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Sharpness Lattice

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem finiteCutExteriorFactor_pos (beta : Real) (S : Finset V)
    (outside : {v : V // v ∉ S} → Bool) :
    0 < finiteCutExteriorFactor G beta S outside := by
  exact Real.exp_pos _

theorem wJ_finiteCutMerge_factor_fixedExterior
    (beta : Real) (S : Finset V)
    (inside : {v : V // v ∈ S} → Bool)
    (outside : {v : V // v ∉ S} → Bool) :
    wJ G.edgeFinset (fun _ => beta) (fun _ => 0)
        (finiteCutMerge S inside outside) =
      finiteCutExteriorFactor G beta S outside *
      wJ (finiteCutGraph G S).edgeFinset (fun _ => beta)
        (fun x => beta * finiteCutBoundaryField G S outside x) inside := by
  rw [wJ_finiteCutMerge_factor]
  congr 1
  unfold finiteCutExteriorFactor
  congr 2
  exact sum_exterior_bond_finiteCutMerge_eq G S inside (fun _ => false) outside


end
end StatMech.FrontierA
