/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/Basic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.Coxeter.Length
import Structure.v1.Atlas.Buildings.code.BNPair.Basic
set_option linter.unusedSectionVars false


/-- The *Bruhat cell* $C(w) = BwB \subseteq G$ associated to $w \in W$: the set of $g$
of the form $b_1 \, n \, b_2$ with $b_1, b_2 \in B$ and $n \in N$ a lift of $w$. -/
def BNPair.bruhatCell {G : Type*} [Group G] {B_idx : Type*}
    {M : CoxeterMatrix B_idx} (bp : BNPair G M) (w : M.Group) : Set G :=
  { g : G | ∃ (b₁ : bp.B) (n : bp.N) (b₂ : bp.B),
    bp.π n = w ∧ g = b₁ * n * b₂ }

/-- Pointwise product $X \cdot Y = \{xy : x \in X, y \in Y\}$ of two subsets of a group. -/
def setMul {G : Type*} [Group G] (X Y : Set G) : Set G :=
  { g | ∃ x ∈ X, ∃ y ∈ Y, g = x * y }

/-- The set of lifts in $N$ of a simple reflection $s \in S$ along $\pi : N \twoheadrightarrow W$. -/
def BNPair.liftSimple {G : Type*} [Group G] {B_idx : Type*}
    {M : CoxeterMatrix B_idx} (bp : BNPair G M) (s : B_idx) : Set G :=
  { (n : G) | ∃ (n' : bp.N), bp.π n' = M.toCoxeterSystem.simple s ∧ n = n' }

