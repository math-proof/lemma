/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ComplexVariables/code/ScoutDeriv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib


example {g : ℂ → ℂ} {U : Set ℂ} {S : Set ℂ}
    (hU : IsOpen U) (hSU : S ⊆ U) (hg : DifferentiableOn ℂ g U) :
    ContinuousOn (deriv g) S :=
  (hg.analyticOnNhd hU).deriv.continuousOn.mono hSU

