/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/CoxeterSystemFromDeletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.OrderOfElement
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.CoxeterSystemFromDeletion
open Function Set


namespace CoxeterSystemFromDeletion

variable {B : Type*} {W : Type*} [Group W]

/-- The Coxeter matrix canonically associated to a family of involutions
$\mathtt{gen} : B \to W$ with no nontrivial relations $\mathtt{gen}\,s
\cdot \mathtt{gen}\,t = 1$ for $s \ne t$: the $(s,t)$-entry is the order of
$\mathtt{gen}\,s \cdot \mathtt{gen}\,t$ in $W$. -/
noncomputable def deletionCoxeterMatrix
    (gen : B → W) (hgen_inv : ∀ s, gen s * gen s = 1)
    (hgen_ne : ∀ s t, s ≠ t → gen s * gen t ≠ 1) : CoxeterMatrix B where
  M := Matrix.of fun s t => orderOf (gen s * gen t)
  isSymm := by
    ext s t
    simp only [Matrix.of_apply, Matrix.transpose_apply]
    exact (orderOf_mul_comm_of_involution gen hgen_inv s t).symm
  diagonal s := by
    simp only [Matrix.of_apply]
    rw [hgen_inv s, orderOf_one]
  off_diagonal s t hne := by
    simp only [Matrix.of_apply]
    intro h
    exact hgen_ne s t hne (orderOf_eq_one_iff.mp h)

end CoxeterSystemFromDeletion
