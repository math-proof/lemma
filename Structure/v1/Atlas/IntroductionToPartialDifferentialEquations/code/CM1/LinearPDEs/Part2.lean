/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM1/LinearPDEs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM1.LinearPDEs.Part2


/-- A PDE of order $N$ in $n$ variables (Definition 1.0.1): an equation $F(\text{jet}) = 0$
where $F$ is a real-valued function of the $N$-jet $(u, \partial^{\alpha} u, x)$. -/
structure PDE (n : ℕ) (N : ℕ) where
  F : PDEJet n N → ℝ

/-- A linear differential operator of order at most $N$ on $\mathbb{R}^n$
(Definition 4.0.2): specified by coefficient functions $a_{\alpha}(x)$ for each multi-index
$\alpha$ with $|\alpha| \le N$, acting on a function $u$ as
$\mathcal{L} u = \sum_{|\alpha| \le N} a_{\alpha}(x) \partial^{\alpha} u$. -/
structure LinearDifferentialOperator (n : ℕ) (N : ℕ) where
  coeff : { α : MultiIndex' n // multiIndexOrder α ≤ N } → ((Fin n → ℝ) → ℝ)

