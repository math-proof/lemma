/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TraceNorm.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
variable (K : Type*) (L : Type*) [CommRing K] [CommRing L] [Algebra K L]


/-- The $K$-linear map $L \to L$ given by left multiplication by $\alpha \in L$. -/
noncomputable abbrev mulLeft (α : L) : L →ₗ[K] L :=
  (Algebra.lmul K L) α

