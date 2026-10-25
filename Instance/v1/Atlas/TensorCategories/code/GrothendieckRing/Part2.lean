/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckRing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.FrobeniusPerron.Part6
import Lemma.Category.Atlas.v1.TensorCategories.code.FrobeniusPerron
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Ring.Defs
import Theorem.v1.Atlas.TensorCategories.code.GrothendieckRing
set_option maxHeartbeats 800000

open Finset


namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : FusionRing ι)

namespace GrRingOf

variable {R : FusionRing ι}

/-- The Grothendieck ring `GrRingOf R` of a fusion ring `R` is a `Ring`. -/
instance instRing : Ring (GrRingOf R) where
  add_assoc a b c := by ext k; simp [add_assoc]
  zero_add a := by ext k; simp
  add_zero a := by ext k; simp
  nsmul := fun n a => ⟨fun k => n • a.coeff k⟩
  nsmul_zero a := by ext k; simp
  nsmul_succ n a := by ext k; simp [add_mul, add_comm]
  add_comm a b := by ext k; simp [add_comm]
  mul_assoc a b c := by
    ext k
    show (R.grMul (R.grMul a.coeff b.coeff) c.coeff) k =
         (R.grMul a.coeff (R.grMul b.coeff c.coeff)) k
    rw [R.grMul_assoc]
  one_mul a := by
    ext k
    show (R.grMul R.grOne a.coeff) k = a.coeff k
    rw [R.grMul_one_left]
  mul_one a := by
    ext k
    show (R.grMul a.coeff R.grOne) k = a.coeff k
    rw [R.grMul_one_right]
  left_distrib a b c := by
    ext k
    show (R.grMul a.coeff (fun k => b.coeff k + c.coeff k)) k =
         (R.grMul a.coeff b.coeff) k + (R.grMul a.coeff c.coeff) k
    rw [R.grMul_left_distrib]
  right_distrib a b c := by
    ext k
    show (R.grMul (fun k => a.coeff k + b.coeff k) c.coeff) k =
         (R.grMul a.coeff c.coeff) k + (R.grMul b.coeff c.coeff) k
    rw [R.grMul_right_distrib]
  zero_mul a := by
    ext k
    show (R.grMul (fun _ => 0) a.coeff) k = 0
    rw [R.grZero_mul]
  mul_zero a := by
    ext k
    show (R.grMul a.coeff (fun _ => 0)) k = 0
    rw [R.grMul_zero]
  neg_add_cancel a := by ext k; simp
  sub_eq_add_neg a b := by ext k; simp [sub_eq_add_neg]
  zsmul := fun n a => ⟨fun k => n • a.coeff k⟩
  zsmul_zero' a := by ext k; simp
  zsmul_succ' n a := by ext k; simp [add_mul, add_comm]
  zsmul_neg' n a := by
    ext k
    show Int.negSucc n • a.coeff k = -((↑(n + 1) : ℤ) • a.coeff k)
    simp [Int.negSucc_eq, Nat.cast_succ]
    ring
  natCast := fun m => ⟨fun k => if k = R.unit then (m : ℤ) else 0⟩
  natCast_zero := by
    ext k
    show (if k = R.unit then (0 : ℤ) else 0) = 0
    split <;> rfl
  natCast_succ m := by
    ext k
    show (if k = R.unit then ((m + 1 : ℕ) : ℤ) else 0) =
         (if k = R.unit then (m : ℤ) else 0) + (if k = R.unit then 1 else 0)
    split <;> simp
  intCast := fun m => ⟨fun k => if k = R.unit then (m : ℤ) else 0⟩
  intCast_ofNat m := by ext k; rfl
  intCast_negSucc m := by
    ext k
    show (if k = R.unit then (Int.negSucc m : ℤ) else 0) =
         -(if k = R.unit then ((m + 1 : ℕ) : ℤ) else 0)
    split <;> simp [Int.negSucc_eq]

end GrRingOf
end FusionRing
