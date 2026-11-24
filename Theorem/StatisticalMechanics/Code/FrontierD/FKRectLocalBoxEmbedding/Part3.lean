module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquare.Part11
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRightStripConnection.Part3
public import Theorem.StatisticalMechanics.Code.FK.FKGeneralQConnectionSymmetry
public import Def.StatisticalMechanics.Code.FrontierD.FKRectLocalBoxEmbedding.Part2
open MeasureTheory StatMech.Lattice StatMech.Percolation SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectLocalBoxEmbedding.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

theorem fkRectReflectedDiagonalSite_mem_box
    {s m : Nat} (hsm : s <= m) :
    fkRectReflectedDiagonalSite s ∈ box 2 m := by
  intro i
  fin_cases i <;> simp [fkRectReflectedDiagonalSite, hsm]

end
end StatMech.FrontierD
