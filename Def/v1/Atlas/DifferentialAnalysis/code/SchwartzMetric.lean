/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzMetric.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.Normed.Group.Tannery
import Theorem.v1.Atlas.DifferentialAnalysis.code.SchwartzComplete
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SchwartzComplete
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SchwartzSeminormsFix
import Theorem.v1.Atlas.DifferentialAnalysis.code.SchwartzSeminormsFix
open scoped SchwartzMap
open Filter


namespace TemperedDistributions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The supremum of all Schwartz seminorms `‖·‖_{m₁, m₂}` for `m₁, m₂ ≤ k`. -/
noncomputable def supSeminorm (k : ℕ) : Seminorm ℝ 𝓢(E, F) :=
  (Finset.Iic (k, k)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2)

/-- The `k`-th term in the metric series: `2⁻ᵏ · s/(1+s)` where `s` is the `k`-th supremum
seminorm of `u - v`. -/
noncomputable def boundedSeminormTerm (k : ℕ) (u v : 𝓢(E, F)) : ℝ :=
  ((1 : ℝ) / 2) ^ k * (supSeminorm k (u - v) /
    (1 + supSeminorm k (u - v)))

/-- The Schwartz metric: `schwartzDist u v = ∑ₖ 2⁻ᵏ · sₖ(u - v) / (1 + sₖ(u - v))` where `sₖ`
is the `k`-th sup seminorm. -/
noncomputable def schwartzDist (u v : 𝓢(E, F)) : ℝ :=
  ∑' k : ℕ, boundedSeminormTerm k u v

end TemperedDistributions
