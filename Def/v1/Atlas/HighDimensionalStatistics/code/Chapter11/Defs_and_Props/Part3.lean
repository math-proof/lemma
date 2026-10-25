/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter11/Defs_and_Props.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Abbrev.v1.Atlas.HighDimensionalStatistics.code.Chapter11.Defs_and_Props.Part2
set_option maxHeartbeats 800000


noncomputable section

open scoped SchwartzMap

open MeasureTheory TemperedDistribution Filter ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace Chapter11

/-- A polynomial symbol `P` is elliptic of order `m` if its degree-`m` homogeneous
component is nonvanishing on `ℝⁿ \ {0}`. -/
def IsElliptic {n : ℕ} (P : MvPolynomial (Fin n) ℂ) (m : ℕ) : Prop :=
  ∀ ξ : Fin n → ℝ, ξ ≠ 0 →
    MvPolynomial.eval (fun i => (ξ i : ℂ)) (MvPolynomial.homogeneousComponent m P) ≠ 0

end Chapter11
end
