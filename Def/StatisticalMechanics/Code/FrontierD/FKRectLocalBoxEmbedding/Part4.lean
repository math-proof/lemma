module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquare.Part11
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRightStripConnection.Part3
public import Theorem.StatisticalMechanics.Code.FK.FKGeneralQConnectionSymmetry
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectLocalBoxEmbedding.Part4
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

def fkRectLocalBoxPositiveDiagonal (s m : Nat) (hsm : s <= m) :
    FK.boxVerts 2 m :=
  ⟨fkRectPositiveDiagonalSite s,
    fkRectPositiveDiagonalSite_mem_box hsm⟩

end
end StatMech.FrontierD
