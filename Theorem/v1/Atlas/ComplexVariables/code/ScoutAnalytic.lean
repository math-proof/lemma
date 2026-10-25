/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ComplexVariables/code/ScoutAnalytic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open Complex Filter Topology


#check @DifferentiableOn.analyticAt
#check @Differentiable.analyticAt
#check @analyticAt_iff_eventually_differentiableAt
#check @AnalyticAt.differentiableAt
#check @DifferentiableOn.analyticOnNhd
#check @AnalyticOnNhd.deriv


example {g : ℂ → ℂ} (h : Differentiable ℂ g) (z : ℂ) : AnalyticAt ℂ g z :=
  h.analyticAt z


example {g : ℂ → ℂ} {s : Set ℂ} {z : ℂ}
    (hd : DifferentiableOn ℂ g s) (hz : s ∈ 𝓝 z) :
    AnalyticAt ℂ g z :=
  hd.analyticAt hz


example {g : ℂ → ℂ} {z : ℂ} :
    AnalyticAt ℂ g z ↔ ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ g w :=
  analyticAt_iff_eventually_differentiableAt


example {g : ℂ → ℂ} {z : ℂ} (h : AnalyticAt ℂ g z) : DifferentiableAt ℂ g z :=
  h.differentiableAt

