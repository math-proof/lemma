/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/LopsidedLLL.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Data.Finset.Basic
set_option maxHeartbeats 800000

open MeasureTheory ProbabilityTheory ENNReal Set Finset

namespace LopsidedLLL

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The event that all events $A_j$ for $j \in S$ fail to occur, i.e. $\bigcap_{j \in S} A_j^c$. -/
def avoidSet {ι : Type*} (A : ι → Set Ω) (S : Finset ι) : Set Ω :=
  ⋂ j ∈ (S : Set ι), (A j)ᶜ
