/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MainLemmaFF.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open Finset


namespace MainLemmaFF

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The indicator function $\mathbf{1}_L(x)$ of a line $L \subseteq \mathbb{F}_q^2$,
valued in $\mathbb{R}$. -/
noncomputable def lineIndicator (L : Finset (F × F))
    (x : F × F) : ℝ :=
  if x ∈ L then 1 else 0

/-- The mean-zero indicator residue $\mathbf{1}_L(x) - 1/q$ of a single line
$L \subseteq \mathbb{F}_q^2$ (with $q = |\mathbb{F}|$). -/
noncomputable def lineHighFreq (L : Finset (F × F))
    (x : F × F) : ℝ :=
  (if x ∈ L then (1 : ℝ) else 0) - (Fintype.card F : ℝ)⁻¹

/-- The line counting function $L(x) = \sum_{L \in \mathcal{L}} \mathbf{1}_L(x)$
on $\mathbb{F}_q^2$. -/
noncomputable def lineSumFunc (ℒ : Finset (Finset (F × F)))
    (x : F × F) : ℝ :=
  ∑ L ∈ ℒ, lineIndicator L x

/-- The constant (zero-frequency) part $L_0 = |\mathcal{L}| / q$ of the line counting
function (independent of `x`). -/
noncomputable def constPart (ℒ : Finset (Finset (F × F)))
    (_x : F × F) : ℝ :=
  (ℒ.card : ℝ) / (Fintype.card F : ℝ)

/-- The high-frequency part $L_h(x) = \sum_{L \in \mathcal{L}} (\mathbf{1}_L(x) - 1/q)$
of the line counting function. -/
noncomputable def highFreqPart (ℒ : Finset (Finset (F × F)))
    (x : F × F) : ℝ :=
  ∑ L ∈ ℒ, lineHighFreq L x

end MainLemmaFF
