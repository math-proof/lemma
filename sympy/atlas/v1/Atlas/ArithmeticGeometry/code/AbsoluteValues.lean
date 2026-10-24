/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AbsoluteValues.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

/-- An absolute value on a field $k$ is an `AbsoluteValue` with codomain $\mathbb{R}$. -/
abbrev AbsoluteValueOnField (k : Type*) [Field k] := AbsoluteValue k ℝ

namespace AbsoluteValueOnField

variable {k : Type*} [Field k] (v : AbsoluteValueOnField k)

/-- Definition 5.5: two absolute values $v_1, v_2$ on $k$ are *equivalent* if there exists
$\alpha > 0$ such that $v_2(x) = v_1(x)^\alpha$ for every $x \in k$. -/
def AreEquivalent (v₁ v₂ : AbsoluteValue k ℝ) : Prop :=
  ∃ α : ℝ, 0 < α ∧ ∀ x : k, v₂ x = (v₁ x) ^ α
