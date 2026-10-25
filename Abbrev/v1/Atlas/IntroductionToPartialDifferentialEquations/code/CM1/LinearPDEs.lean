/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM1/LinearPDEs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib


/-- A multi-index in $n$ variables is a function $\alpha : \{1, \ldots, n\} \to \mathbb{N}$
recording the order of differentiation in each coordinate. -/
abbrev MultiIndex' (n : ℕ) := Fin n → ℕ

