/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/ParsevalHighFreq.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open Finset Complex ZMod


namespace ProjectionTheory

variable {p : ℕ} [NeZero p]

/-- The high-frequency part of `g : ZMod p → ℂ`: the function `g` with its mean
removed, $g_h(a) = g(a) - \tfrac{1}{p}\sum_b g(b)$. This is the orthogonal complement
of the constant (zero-frequency) component $g_0$ in the decomposition $g = g_0 + g_h$. -/
noncomputable def highFreqPart (g : ZMod p → ℂ) : ZMod p → ℂ :=
  fun a => g a - (↑p)⁻¹ * (∑ b : ZMod p, g b)

end ProjectionTheory
