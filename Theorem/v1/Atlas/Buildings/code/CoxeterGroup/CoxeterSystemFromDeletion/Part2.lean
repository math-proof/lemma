/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/CoxeterSystemFromDeletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.OrderOfElement
import Def.v1.Atlas.Buildings.code.CoxeterGroup.CoxeterSystemFromDeletion
open Function Set


namespace CoxeterSystemFromDeletion

variable {B : Type*} {W : Type*} [Group W]

/-- The family $\mathtt{gen}$ satisfies the lifting hypothesis for the
canonically associated Coxeter matrix: each pairwise relation
$(\mathtt{gen}\,s \cdot \mathtt{gen}\,t)^{m(s,t)} = 1$ holds tautologically by
the definition of order. -/
theorem deletionCoxeterMatrix_isLiftable
    (gen : B → W) (hgen_inv : ∀ s, gen s * gen s = 1)
    (hgen_ne : ∀ s t, s ≠ t → gen s * gen t ≠ 1) :
    (deletionCoxeterMatrix gen hgen_inv hgen_ne).IsLiftable gen := by
  intro s t
  show (gen s * gen t) ^ (Matrix.of fun s' t' => orderOf (gen s' * gen t')) s t = 1
  simp only [Matrix.of_apply]
  exact pow_orderOf_eq_one _

end CoxeterSystemFromDeletion
