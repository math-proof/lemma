/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PolygonWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Onsager.PolygonWalk.Part3


namespace StatMech.Onsager.PolygonWalk

theorem cross_congr_dirCode (a b : Pt) (ha : isUnitDir a) (hb : isUnitDir b)
    (hnu : b ≠ (-a.1, -a.2)) :
    ((cross a b : ℤ) : ZMod 4) = dirCode b - dirCode a := by
  rcases ha with h | h | h | h <;> rcases hb with h' | h' | h' | h' <;>
    subst h <;> subst h' <;> revert hnu <;> decide


theorem cornerBalance_mod4 {n : ℕ} [NeZero n] (dir : Fin n → Pt)
    (hunit : ∀ i, isUnitDir (dir i))
    (hnu : ∀ i, dir (i + 1) ≠ (-(dir i).1, -(dir i).2)) :
    ((cornerBalance (fun i => cross (dir i) (dir (i + 1))) : ℤ) : ZMod 4) = 0 := by
  unfold cornerBalance
  rw [Int.cast_sum]
  have hstep : ∀ i : Fin n,
      ((cross (dir i) (dir (i + 1)) : ℤ) : ZMod 4)
        = dirCode (dir (i + 1)) - dirCode (dir i) := by
    intro i; exact cross_congr_dirCode _ _ (hunit i) (hunit (i + 1)) (hnu i)
  rw [Finset.sum_congr rfl (fun i _ => hstep i)]
  
  rw [Finset.sum_sub_distrib]
  have hreindex : ∑ i : Fin n, dirCode (dir (i + 1)) = ∑ i : Fin n, dirCode (dir i) :=
    Equiv.sum_comp (Equiv.addRight (1 : Fin n)) (fun i => dirCode (dir i))
  rw [hreindex, sub_self]

end StatMech.Onsager.PolygonWalk
