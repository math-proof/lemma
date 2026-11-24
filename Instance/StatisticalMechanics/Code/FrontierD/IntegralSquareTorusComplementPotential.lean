module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedBoundaryOpenPathPotential
public import Theorem.StatisticalMechanics.Code.FrontierD.IntegralSquareTorusComplementPotential


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusComplementPotential.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

open StatMech.Onsager

open IntegralSquareTorusCycle

noncomputable section

variable {L : Nat} [Fact (8 < L)]

instance complementPotentialFactTwo : Fact (2 < L) := ⟨by
  have hL : 8 < L := Fact.out
  omega⟩


end
end StatMech.FrontierD
