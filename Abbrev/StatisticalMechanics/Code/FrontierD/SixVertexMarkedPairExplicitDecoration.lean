module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall.Part4
public import Instance.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairExplicitDecoration
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairExplicitDecoration.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

abbrev MarkedBinaryDecoration (Site : Type*) [Fintype Site]
    [DecidableEq Site] (k : Nat) :=
  Sigma fun marked : {s : Finset Site // s.card = k} =>
    ({site : Site // site ∉ marked.1} -> Bool)

end
end StatMech.FrontierD
