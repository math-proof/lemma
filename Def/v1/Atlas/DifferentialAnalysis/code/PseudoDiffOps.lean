/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/PseudoDiffOps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.DifferentialAnalysis.code.DifferentialOperators.Part2
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.DifferentialOperators
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.ConvolutionTheorem
import Def.v1.Atlas.DifferentialAnalysis.code.ConvolutionTheorem
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.Compactness.LocallyCompact


noncomputable section

open scoped SchwartzMap Pointwise

open MeasureTheory Set Function TemperedDistribution

namespace DifferentialOperators

variable {n : ℕ}

/-- A tempered distribution `u` on Euclidean space has compact support if there is a
compact `K` such that `u` annihilates every Schwartz function whose support is disjoint
from `K`. -/
def HasCompactSupport (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : Prop :=
  ∃ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K ∧
    ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      (Function.support (⇑φ) ∩ K = ∅) → u φ = 0

end DifferentialOperators
end
