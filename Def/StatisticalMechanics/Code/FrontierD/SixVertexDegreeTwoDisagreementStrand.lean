module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementComponentCType.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology.Part4
public import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusMedial.Part5
public import Mathlib.Algebra.Group.End
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Factors
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def sixVertexLocalDisagreementSides
    (p q : SixVertexLocalIncomingPattern) : Finset (Fin 4) :=
  Finset.univ.filter fun d => p d != q d

end
end StatMech.FrontierD
