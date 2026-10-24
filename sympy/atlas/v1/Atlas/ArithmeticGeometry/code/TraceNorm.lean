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

/-- The trace map $\mathrm{Tr}_{L/K} : L \to K$ of the algebra $L$ over $K$. -/
noncomputable def traceOfExtension : L →ₗ[K] K :=
  Algebra.trace K L

/-- The norm map $\mathrm{N}_{L/K} : L \to K$ of the algebra $L$ over $K$. -/
noncomputable def normOfExtension : L →* K :=
  Algebra.norm K
