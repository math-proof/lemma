/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM1/LinearPDEs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM1.LinearPDEs.Part3


namespace LinearDifferentialOperator

/-- A linear PDE of order $N$ on $\mathbb{R}^n$ (Definition 4.0.3): an equation
$\mathcal{L} u = f(x)$ specified by a linear differential operator $\mathcal{L}$ and a
source function $f$. -/
structure LinearPDE (n : ℕ) (N : ℕ) where
  L : LinearDifferentialOperator n N
  f : (Fin n → ℝ) → ℝ

end LinearDifferentialOperator
