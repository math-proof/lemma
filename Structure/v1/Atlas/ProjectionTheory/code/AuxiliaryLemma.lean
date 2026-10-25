/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/AuxiliaryLemma.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open Finset


namespace IncidenceGeometry

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- An affine line in `(ℤ/p)^2`, represented by coefficients `(a, b, c)` defining the
equation `a·x + b·y = c`. The nondegeneracy condition `a ≠ 0 ∨ b ≠ 0` ensures the
equation truly cuts out a line. -/
structure AffineLine (p : ℕ) [Fact (Nat.Prime p)] where
  a : ZMod p
  b : ZMod p
  c : ZMod p
  nondegenerate : a ≠ 0 ∨ b ≠ 0

end IncidenceGeometry
