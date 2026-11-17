/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/PerronFrobeniusProof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Convex.StdSimplex
public import Theorem.v1.Atlas.TensorCategories.code.PerronFrobeniusProof

@[expose] public section

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
