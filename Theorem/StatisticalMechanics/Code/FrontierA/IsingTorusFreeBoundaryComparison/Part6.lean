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
import Def.StatisticalMechanics.Code.FrontierA.IsingTorusFreeBoundaryComparison.Part6
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Sharpness Lattice

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem finiteCutConditionalTwoPoint_le_plus
    (beta : Real) (hbeta : 0 ≤ beta) (S : Finset V)
    (outside : {v : V // v ∉ S} → Bool)
    (x y : {v : V // v ∈ S}) :
    finiteCutConditionalTwoPoint G beta S outside x y ≤
      finiteCutPlusTwoPoint G beta S x y := by
  unfold finiteCutConditionalTwoPoint finiteCutPlusTwoPoint
  apply ginibre_boundary_twoPoint_mono
  · intro e he
    exact hbeta
  · intro z
    rw [abs_mul, abs_of_nonneg hbeta]
    exact mul_le_mul_of_nonneg_left
      (abs_finiteCutBoundaryField_le_plus G S outside z) hbeta


end
end StatMech.FrontierA
