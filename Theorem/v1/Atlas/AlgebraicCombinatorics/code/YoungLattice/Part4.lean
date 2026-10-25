/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/YoungLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicCombinatorics.code.SpernerProperty.Part2
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.SpernerProperty
import Mathlib.Order.Cover
import Mathlib.Order.Grade
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Ring
import Def.v1.Atlas.AlgebraicCombinatorics.code.YoungLattice.Part3
set_option autoImplicit false

open SpernerProperty


namespace YoungLattice

namespace Lmn

lemma sumParts_complement_add {m n : ℕ} (p : Lmn m n) :
    sumParts p.complement + sumParts p = m * n := by
  unfold sumParts complement
  have hreindex : ∑ x : Fin m, (p.val x).val = ∑ x : Fin m, (p.val (Fin.rev x)).val :=
    Fintype.sum_equiv Fin.revPerm (fun x => (p.val x).val) (fun x => (p.val (Fin.rev x)).val)
      (fun i => by simp [Fin.revPerm])
  rw [hreindex, ← Finset.sum_add_distrib]
  simp_rw [Nat.sub_add_cancel (Nat.lt_succ_iff.mp (p.val (Fin.rev _)).isLt)]
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

lemma grade_le_mul {m n : ℕ} (p : Lmn m n) : grade ℕ p ≤ m * n := by
  rw [grade_eq]; have := sumParts_complement_add p; omega

end Lmn
end YoungLattice
