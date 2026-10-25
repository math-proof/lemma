/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/PoissonUniqueness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.DifferentialAnalysis.code.DifferentialOperators.Part2
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.DifferentialOperators
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Group.Bounded


noncomputable section

open Filter Topology

namespace DifferentialOperators

variable {n : ℕ}

/-- A complex-valued function on Euclidean space is harmonic if it is smooth and its
Laplacian (sum of pure second partial derivatives along the standard basis directions)
vanishes everywhere. -/
def IsHarmonic (u : EuclideanSpace ℝ (Fin n) → ℂ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) u ∧
    ∀ x : EuclideanSpace ℝ (Fin n),
      ∑ j : Fin n, (fderiv ℝ (fderiv ℝ u) x)
        (EuclideanSpace.single j 1) (EuclideanSpace.single j 1) = 0

end DifferentialOperators
end
