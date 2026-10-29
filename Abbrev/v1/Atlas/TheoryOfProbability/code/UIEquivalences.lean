/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/UIEquivalences.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Function.UniformIntegrable
import Def.v1.Atlas.TheoryOfProbability.code.UIEquivalences
open scoped MeasureTheory NNReal ENNReal
open MeasureTheory


namespace TheoryOfProbability3

variable {α : Type*} {ι : Type*} {m : MeasurableSpace α} {μ : Measure α}

/-- Uniform absolute continuity of the `L¹` integrals of a family `f : ι → α → ℝ`,
expressed via Mathlib's `UnifIntegrable f 1 μ`. -/
abbrev UnifAbsContIntegrals (f : ι → α → ℝ) (μ : Measure α) : Prop :=
  UnifIntegrable f 1 μ

/-- A uniform `L¹`-bound on the family `f : ι → α → ℝ`:
there exists `C : NNReal` with `‖f i‖₁ ≤ C` for all `i`. -/
abbrev UnifL1Bound (f : ι → α → ℝ) (μ : Measure α) : Prop :=
  ∃ C : NNReal, ∀ i, eLpNorm (f i) 1 μ ≤ ↑C

end TheoryOfProbability3
