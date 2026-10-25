/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/OrthogonalityLines.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open Finset


namespace OrthogonalityLines

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- The high-frequency part of the characteristic function $\mathbf{1}_L$ of a (would-be)
line $L \subseteq \mathbb{F}_p^2$: $L_h(x) = \mathbf{1}_L(x) - 1/p$. For an actual affine line
of cardinality $p$, this subtracts the average value $|L|/p^2 = 1/p$. -/
noncomputable def lineHighFreq (L : Finset (ZMod p × ZMod p)) (x : ZMod p × ZMod p) : ℝ :=
  (if x ∈ L then (1 : ℝ) else 0) - (p : ℝ)⁻¹

/-- The affine line $\{(x, y) \in \mathbb{F}_p^2 \mid a x + b y = c\}$. -/
noncomputable def affineLine (a b c : ZMod p) : Finset (ZMod p × ZMod p) :=
  Finset.univ.filter (fun xy => a * xy.1 + b * xy.2 = c)

/-- A finite subset $L \subseteq \mathbb{F}_p^2$ is an *affine line* if there exist
coefficients $(a, b) \ne (0, 0)$ and $c \in \mathbb{F}_p$ with $L = \{a x + b y = c\}$. -/
def IsAffineLine (L : Finset (ZMod p × ZMod p)) : Prop :=
  ∃ a b c : ZMod p, (a, b) ≠ (0, 0) ∧ L = affineLine a b c

end OrthogonalityLines
