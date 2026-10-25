/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Monotonic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.FKG
import Theorem.StatisticalMechanics.Code.OSSS.Monotonic.Part3
open Finset


namespace StatMech

namespace OSSS.Monotonic

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def condProbOpen (μ : ConfigSpace E → ℝ) (F : Finset E)
    (η : ConfigSpace E) (e : E) : ℝ :=
  ∑ ω, (OpenAt e).indicator (fun _ => (1 : ℝ)) ω * condMass μ F η ω


def IsMonotonicMeasure (μ : ConfigSpace E → ℝ) : Prop :=
  ∀ (e : E) (F : Finset E) (ξ ζ : ConfigSpace E), (∀ f ∈ F, ξ f ≤ ζ f) →
    0 < condNorm μ F ξ → 0 < condNorm μ F ζ →
    condProbOpen μ F ξ e ≤ condProbOpen μ F ζ e


end OSSS.Monotonic
end StatMech
