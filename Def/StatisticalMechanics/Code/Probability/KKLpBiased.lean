module
public import Theorem.StatisticalMechanics.Code.TwoDim.KKLWire.Part2
public import Theorem.StatisticalMechanics.Code.Probability.RhoOptimiseClose2
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLpBiased.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Probability

open ConfigSpace Function Finset StatMech StatMech.OSSS

variable {E : Type*} [Fintype E] [DecidableEq E]


def kpb_flipAll (ω : ConfigSpace E) : ConfigSpace E := fun e => !(ω e)

end Probability
end StatMech
