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
import Def.v1.Atlas.DifferentialAnalysis.code.SchwartzMetric
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SchwartzMetric
import Theorem.v1.Atlas.DifferentialAnalysis.code.SchwartzCompleteness
open scoped SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]


namespace TemperedDistributions

open Filter Topology in

/-- Completeness of the Schwartz space `𝓢(E, F)` as a Mathlib `CompleteSpace` instance
(Melrose Prop. 6.7). -/
noncomputable instance instCompleteSpace : CompleteSpace 𝓢(E, F) :=
  instCompleteSpace_axiom

end TemperedDistributions
