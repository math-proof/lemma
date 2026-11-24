module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDevelopedWinding.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetFull.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareDevelopment.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def fkRectSquareDeckLattice (R : FKRectTorus) :
    AddSubgroup (Int × Int) :=
  (fkRectSquareDeckHom R).range

end
end StatMech.FrontierD
