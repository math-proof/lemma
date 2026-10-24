/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/HighFreqMultConv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.ProjectionTheory.code.LinnikLargeSieve
import Lemma.Real.Atlas.v1.ProjectionTheory.code.LinnikLargeSieve
import Lemma.Real.Atlas.v1.ProjectionTheory.code.MultiplicativeConvolution
import sympy.atlas.v1.Atlas.ProjectionTheory.code.MultiplicativeConvolution

open Finset Complex BigOperators

noncomputable section

namespace HighFreqMultConv

variable (q : ℕ) [NeZero q]

/-- The *multiplicative convolution* on the group of units `(ZMod q)ˣ`:
$(f *_M g)(a) = \sum_{b \in (\mathbb{Z}/q)^\times} f(b)\, g(a/b)$. -/
def mulConvUnits (f g : (ZMod q)ˣ → ℂ) (a : (ZMod q)ˣ) : ℂ :=
  ∑ b : (ZMod q)ˣ, f b * g (a / b)

/-- The *high-frequency part* `f_h = f - f₀` of a function on `(ZMod q)ˣ`, where `f₀`
is the constant function equal to the average $\langle f \rangle = \frac{1}{|(\mathbb{Z}/q)^\times|}\sum_b f(b)$. -/
def highFreqUnits (f : (ZMod q)ˣ → ℂ) (a : (ZMod q)ˣ) : ℂ :=
  f a - (∑ b : (ZMod q)ˣ, f b) / (Fintype.card (ZMod q)ˣ : ℂ)
