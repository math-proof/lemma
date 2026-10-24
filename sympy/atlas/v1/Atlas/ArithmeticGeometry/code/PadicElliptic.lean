/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicElliptic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Monotone.Basic

noncomputable section

open scoped Padic


attribute [local instance] Classical.dec

namespace PadicElliptic

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- The group of $\mathbb{Q}_p$-points of a Weierstrass curve $W$ defined over $\mathbb{Q}$,
obtained by base-changing to $\mathbb{Q}_p$ and taking the affine point set. -/
abbrev PadicPointGroup (W : WeierstrassCurve ℚ) : Type :=
  (W.baseChange ℚ_[p]).toAffine.Point

/-- Membership predicate for the $n$-th piece $E_n(\mathbb{Q}_p)$ of the $p$-adic filtration:
a point is either the identity, or has $y \ne 0$ and $v_p(x) - v_p(y) \ge n$. -/
def InPadicFiltration (W : WeierstrassCurve ℚ) (n : ℕ)
    (P : PadicPointGroup W (p := p)) : Prop :=
  match P with
  | .zero => True
  | .some x y _ => y ≠ 0 ∧ (n : ℤ) ≤ Padic.valuation x - Padic.valuation y

/-- The $p$-adic valuation on $\mathbb{Q}_p$ is invariant under negation: $v_p(-y) = v_p(y)$. -/
lemma padic_valuation_neg (y : ℚ_[p]) : (-y).valuation = y.valuation := by
  by_cases hy : y = 0
  · simp [hy]
  · have hny : -y ≠ 0 := neg_ne_zero.mpr hy
    have hnorm : ‖(-y)‖ = ‖y‖ := norm_neg y
    rw [Padic.norm_eq_zpow_neg_valuation hny, Padic.norm_eq_zpow_neg_valuation hy] at hnorm
    have hp1 : (1 : ℝ) < p := by exact_mod_cast Nat.Prime.one_lt hp.out
    have hp_pos : (0 : ℝ) < p := lt_trans zero_lt_one hp1
    have hp_ne_one : (p : ℝ) ≠ 1 := ne_of_gt hp1
    have := zpow_right_injective₀ hp_pos hp_ne_one hnorm
    linarith
