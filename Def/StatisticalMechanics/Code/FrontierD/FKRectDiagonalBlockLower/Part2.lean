/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDiagonalBlockLower.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKFiniteConnectionApproximation
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectLocalBoxEmbedding.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectWindingBlockSource.Part3
import Theorem.StatisticalMechanics.Code.FK.TwoPointPathLower
import Theorem.StatisticalMechanics.Code.FrontierD.FiniteProductExceptions
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDiagonalBlockLower


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation Filter Topology

noncomputable section

def fkRectWindingBlockBadIndices (blocks m : Nat) :
    Finset (Fin (blocks + 1)) :=
  (Finset.univ.filter fun i => i.val < m) ∪
    (Finset.univ.filter fun i => blocks - i.val < m)

end
end StatMech.FrontierD
