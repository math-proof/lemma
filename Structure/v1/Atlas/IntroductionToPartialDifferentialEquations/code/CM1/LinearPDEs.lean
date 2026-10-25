/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM1/LinearPDEs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Instance.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM1.LinearPDEs


/-- The $N$-jet of a function at a point: stores the base point $x \in \mathbb{R}^n$ and
the values of all partial derivatives $\partial^{\alpha} u(x)$ with $|\alpha| \le N$.
This is the data on which a PDE of order $N$ acts (Definition 1.0.1). -/
structure PDEJet (n : ℕ) (N : ℕ) where
  point : Fin n → ℝ
  derivatives : { α : MultiIndex' n // multiIndexOrder α ≤ N } → ℝ

