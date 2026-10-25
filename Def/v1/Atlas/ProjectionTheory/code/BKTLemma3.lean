/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/BKTLemma3.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib


namespace BKTProof

open Finset Complex

/-- The squared $L^2$-norm of the high-frequency part of `f` on a finite set `S`,
i.e. `∑_{x ∈ S} |f(x) − μ_S(f)|²`, where `μ_S(f) = (1/|S|) ∑_{y ∈ S} f(y)` is the average
of `f` over `S`. This is `‖f_h‖_{L^2(S)}²` in the notation of BKT. -/
noncomputable def l2NormSqHighFreq {α : Type*} (S : Finset α) (f : α → ℂ) : ℝ :=
  ∑ x ∈ S, ‖f x - ((S.card : ℂ)⁻¹ * ∑ y ∈ S, f y)‖ ^ 2

/-- The high-frequency $L^2$-norm of `f` on a finite set `S`, namely
`‖f_h‖_{L^2(S)} = √(∑_{x ∈ S} |f(x) − μ_S(f)|²)`. -/
noncomputable def l2NormHighFreq {α : Type*} (S : Finset α) (f : α → ℂ) : ℝ :=
  Real.sqrt (l2NormSqHighFreq S f)

end BKTProof
