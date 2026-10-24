/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MainLemma2F.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.ProjectionTheory.code.FourierFF
import Lemma.Real.Atlas.v1.ProjectionTheory.code.FourierFF
import Lemma.Real.Atlas.v1.ProjectionTheory.code.OrthogonalityLines
import Lemma.Real.Atlas.v1.ProjectionTheory.code.ParsevalFF
import sympy.atlas.v1.Atlas.ProjectionTheory.code.OrthogonalityLines

open Finset

namespace LineSumDecomposition

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- The line counting function $f(x) = \sum_{L \in \mathcal{L}} \mathbf{1}_L(x)$,
counting how many lines from $\mathcal{L}$ pass through the point $x \in \mathbb{F}_p^2$. -/
noncomputable def lineSumFn (ℒ : Finset (Finset (ZMod p × ZMod p)))
    (x : ZMod p × ZMod p) : ℝ :=
  ∑ L ∈ ℒ, if x ∈ L then 1 else 0

/-- The constant (zero-frequency) part $f_0 = |\mathcal{L}| / p$ in the Fourier
decomposition $f = f_0 + f_h$ of the line counting function. -/
noncomputable def lineSumConst (ℒ : Finset (Finset (ZMod p × ZMod p))) : ℝ :=
  (ℒ.card : ℝ) / (p : ℝ)

/-- The high-frequency part $f_h = f - f_0$ of the line counting function, i.e. the
mean-zero remainder after subtracting the constant component. -/
noncomputable def lineSumHighFreq (ℒ : Finset (Finset (ZMod p × ZMod p)))
    (x : ZMod p × ZMod p) : ℝ :=
  lineSumFn ℒ x - lineSumConst ℒ
