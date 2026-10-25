/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLpBiased.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.TwoDim.KKLWire.Part2
import Theorem.StatisticalMechanics.Code.Probability.RhoOptimiseClose2
import Theorem.StatisticalMechanics.Code.Probability.KKLpBiased
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Probability

open ConfigSpace Function Finset StatMech StatMech.OSSS

variable {E : Type*} [Fintype E] [DecidableEq E]


def kpb_PBiasedHC (q : ℝ) : Prop :=
  ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, KKLHypercontractive p 2


end Probability
end StatMech
