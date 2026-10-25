/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QBinomial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic
import Def.v1.Atlas.TensorCategories.code.QBinomial
set_option maxHeartbeats 400000

variable {k : Type*} [Field k]


/-- The q-binomial coefficient `qBinomial q n m` vanishes when `n < m`. -/
lemma qBinomial_eq_zero_of_lt (q : k) (n m : ℕ) (h : n < m) : qBinomial q n m = 0 := by
  induction n, m using qBinomial.induct with
  | case1 n => omega
  | case2 n => simp [qBinomial]
  | case3 n m ih1 ih2 =>
    rw [qBinomial, ih1 (by omega), ih2 (by omega)]; simp

/-- The q-binomial coefficient `qBinomial q n n` equals `1`. -/
lemma qBinomial_self (q : k) : ∀ n : ℕ, qBinomial q n n = 1 := by
  intro n; induction n with
  | zero => simp [qBinomial]
  | succ n ih =>
    rw [qBinomial, qBinomial_eq_zero_of_lt q n (n + 1) (by omega)]; simp [ih]

