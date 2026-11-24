module
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Finset.Max
public import Def.StatisticalMechanics.Code.FrontierA.GrahamGateDiscrepancy.Part9


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

theorem RelationPartialMatching.HoleState.occupantAt_spec
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (state : RelationPartialMatching.HoleState r) (b : B)
    (hincident : r state.hole b) :
    state.matching.toFun (state.occupantAt b hincident) = some b :=
  Classical.choose_spec (state.maximum.saturates_target_of_unmatched
    state.hole state.hole_unmatched b hincident)


end StatMech.FrontierA
