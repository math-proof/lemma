/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFaceEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4OuterLeafDual.Part7
import Theorem.StatisticalMechanics.Code.FK.OffCentreDomination.Part13
import Theorem.StatisticalMechanics.Code.Lattice.ClusterContourBijection.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFaceEmbedding
open Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising StatMech.FK

noncomputable section

theorem fkSquareBox_innerFaceMap_injective
    {N m : Nat} (hNm : N < m) :
    Function.Injective (fkSquareBox_innerFaceMap N m) := by
  intro x y hxy
  apply Subtype.ext
  exact (pfdFace_eq_inner_iff hNm y.2).mp hxy


end
end StatMech.FrontierD
