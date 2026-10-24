/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/ContinuousFunctions/Continuity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace ContinuousFunctions

/-- `AchievesAbsMin f S c` states that `f` achieves its absolute minimum on `S` at the point `c`,
i.e. `c ∈ S` and `f c ≤ f x` for every `x ∈ S`. -/
def AchievesAbsMin (f : ℝ → ℝ) (S : Set ℝ) (c : ℝ) : Prop :=
  c ∈ S ∧ ∀ x ∈ S, f c ≤ f x

/-- `AchievesAbsMax f S d` states that `f` achieves its absolute maximum on `S` at the point `d`,
i.e. `d ∈ S` and `f x ≤ f d` for every `x ∈ S`. -/
def AchievesAbsMax (f : ℝ → ℝ) (S : Set ℝ) (d : ℝ) : Prop :=
  d ∈ S ∧ ∀ x ∈ S, f x ≤ f d

/-- `IsBoundedOn f S` states that `f` is bounded on `S`: there exists a nonnegative real
number `B` such that `|f x| ≤ B` for every `x ∈ S`. -/
def IsBoundedOn (f : ℝ → ℝ) (S : Set ℝ) : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ S, |f x| ≤ B
