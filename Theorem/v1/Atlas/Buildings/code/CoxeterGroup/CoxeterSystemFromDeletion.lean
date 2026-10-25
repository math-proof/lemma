/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/CoxeterSystemFromDeletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.OrderOfElement
open Function Set


namespace CoxeterSystemFromDeletion

variable {B : Type*} {W : Type*} [Group W]

/-- For involutions $\mathtt{gen}\,s$ and $\mathtt{gen}\,t$, the products
$(\mathtt{gen}\,s)(\mathtt{gen}\,t)$ and $(\mathtt{gen}\,t)(\mathtt{gen}\,s)$
have the same order, since they are conjugate via $\mathtt{gen}\,s$. -/
theorem orderOf_mul_comm_of_involution
    (gen : B → W) (hgen_inv : ∀ s, gen s * gen s = 1) (s t : B) :
    orderOf (gen s * gen t) = orderOf (gen t * gen s) := by
  have h : SemiconjBy (gen s) (gen s * gen t) (gen t * gen s) := by
    show gen s * (gen s * gen t) = gen t * gen s * gen s
    rw [← mul_assoc, hgen_inv, one_mul, mul_assoc, hgen_inv, mul_one]
  exact h.orderOf_eq

end CoxeterSystemFromDeletion
