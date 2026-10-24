/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzCompleteness.lean -/

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
import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.SchwartzMetric
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SchwartzMetric

open scoped SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The Schwartz space `𝓢(E, F)` is complete (Melrose Prop. 6.7 / 7.4-adjacent statement),
stated as a top-level theorem so it can be reused without depending on instance synthesis. -/
theorem instCompleteSpace_axiom :
    CompleteSpace 𝓢(E, F) :=
  instCompleteSpaceSchwartz

namespace TemperedDistributions

open Filter Topology in

/-- Completeness of the Schwartz space `𝓢(E, F)` as a Mathlib `CompleteSpace` instance
(Melrose Prop. 6.7). -/
noncomputable instance instCompleteSpace : CompleteSpace 𝓢(E, F) :=
  instCompleteSpace_axiom

end TemperedDistributions
