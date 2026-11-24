module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
public import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
public import Theorem.StatisticalMechanics.Code.BeffaraDC.SelfDualValue
public import Theorem.StatisticalMechanics.Code.Universality.G3PercDualityFull.Part2
public import Theorem.StatisticalMechanics.Code.RSW.SelfDualityNode
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

noncomputable def rsd_selfDualPoint (q : ℝ) : ℝ := Real.sqrt q / (1 + Real.sqrt q)

end RSW
end StatMech
