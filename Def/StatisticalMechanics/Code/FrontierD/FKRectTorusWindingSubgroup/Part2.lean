module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetMonotonicity
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingSubgroup
open SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingSubgroup.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def FKRectWindingSubgroupRankTwo (R : FKRectTorus)
    (omega : R.Configuration) (x : R.Vertex) : Prop :=
  ∃ u ∈ fkRectClosedWindingSubgroup R omega x,
    ∃ v ∈ fkRectClosedWindingSubgroup R omega x,
      FKRectWindingIndependent u v


end
end StatMech.FrontierD
