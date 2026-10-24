/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/Derivatives/Weierstrass.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open BigOperators Topology in
/-- The **Weierstrass nowhere-differentiable function**
`f(x) = ∑_{k=0}^∞ cos(160^k x) / 4^k`, defined as a `tsum` over the natural numbers. -/
noncomputable def weierstrass_fun (x : ℝ) : ℝ :=
  ∑' k : ℕ, cos (160 ^ k * x) / 4 ^ k
