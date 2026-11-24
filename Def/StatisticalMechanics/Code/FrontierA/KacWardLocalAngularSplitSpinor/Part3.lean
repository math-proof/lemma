module
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardLocalAngularSplit.Part3
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngularSplitSpinor.Part3
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardLocalAngularSplitSpinor.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplitSpinor.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open SimpleGraph

open scoped BigOperators


noncomputable def kwLocalAngularSplitSpinorPhase
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) :=
  kwPhaseGauge (kwLocalAngularSplitSpinorGauge data)
    (kwLocalAngularSplitPhase data)

end StatMech.FrontierA
