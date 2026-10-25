/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/PerronFrobeniusProof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Convex.StdSimplex
import Theorem.v1.Atlas.TensorCategories.code.PerronFrobeniusProof
open Finset BigOperators Matrix

set_option maxHeartbeats 800000


namespace PerronFrobenius

variable {ι : Type*} [DecidableEq ι] [Fintype ι] [Nonempty ι]

/-- Collatz-Wielandt set: pairs `(v, t)` with `v` in the standard simplex, `t ≥ 0`, and
`t * v i ≤ (M.mulVec v) i` for all `i`. The Perron-Frobenius eigenvalue is realised as the
supremum of `t` over this set. -/
def CWSet (M : Matrix ι ι ℝ) : Set ((ι → ℝ) × ℝ) :=
  {p | p.1 ∈ stdSimplex ℝ ι ∧ 0 ≤ p.2 ∧ ∀ i, p.2 * p.1 i ≤ M.mulVec p.1 i}

end PerronFrobenius
