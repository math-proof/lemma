/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ECDLP.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib


section Example_9_1

/-- Probability that the first `n` steps of a random walk on a set of size `N`
all land on distinct vertices (the birthday-product `∏_{i<n} (1 - (i+1)/N)`). -/
noncomputable def birthdayProb (N : ℕ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n, (1 - (↑(i + 1) : ℝ) / ↑N)

/-- Expected value of the rho-length for a random walk on a set of size `N`,
expressed as `∑_{n<N} birthdayProb N n`. Theorem 9.3 shows this is asymptotic to `√(πN/2)`. -/
noncomputable def expectedRho (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, birthdayProb N n

end Example_9_1
