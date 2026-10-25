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

