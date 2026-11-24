module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
public import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
public import Theorem.StatisticalMechanics.Code.BeffaraDC.SelfDualValue
public import Theorem.StatisticalMechanics.Code.Universality.G3PercDualityFull.Part2
public import Theorem.StatisticalMechanics.Code.RSW.SelfDualityNode.Part3
open scoped BigOperators ENNReal NNReal
open MeasureTheory


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/SelfDualityNode.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace RSW

variable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]


def rsd_edgeCompl (ω : ConfigSpace (Sym2 V)) : ConfigSpace (Sym2 V) := fun e => !(ω e)

end RSW
end StatMech
