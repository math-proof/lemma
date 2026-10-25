/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.TensorCategories.code.StarAlgebra
import Lemma.Category.Atlas.v1.TensorCategories.code.StarAlgebra
import Lemma.Category.Atlas.v1.TensorCategories.code.FrobeniusPerron
import Def.v1.Atlas.TensorCategories.code.FrobeniusPerron.Part6
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Theorem.v1.Atlas.TensorCategories.code.StarAlgebraCorollaries
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

open Finset Complex

/-- Corollary 1.43.3: a nonzero idempotent in a finite-dimensional `*`-algebra with trace has
positive real trace. -/


namespace StarAlgWithTrace

variable (B : StarAlgWithTrace)

end StarAlgWithTrace

namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : FusionRing ι)

noncomputable section

namespace GrRingOfC

variable {R : FusionRing ι}

/-- The complexified Grothendieck ring of a fusion ring is a ring. -/
instance instRing : Ring (GrRingOfC R) where
  add_assoc a b c := by ext k; simp [add_assoc]
  zero_add a := by ext k; simp
  add_zero a := by ext k; simp
  nsmul := fun n a => ⟨fun k => n • a.coeff k⟩
  nsmul_zero a := by ext k; simp
  nsmul_succ n a := by ext k; simp [add_mul, add_comm]
  add_comm a b := by ext k; simp [add_comm]
  mul_assoc a b c := by
    ext k
    show (R.grMulC (R.grMulC a.coeff b.coeff) c.coeff) k =
         (R.grMulC a.coeff (R.grMulC b.coeff c.coeff)) k
    rw [R.grMulC_assoc]
  one_mul a := by
    ext k
    show (R.grMulC (fun k => if k = R.unit then 1 else 0) a.coeff) k = a.coeff k
    rw [R.grMulC_one_left]
  mul_one a := by
    ext k
    show (R.grMulC a.coeff (fun k => if k = R.unit then 1 else 0)) k = a.coeff k
    rw [R.grMulC_one_right]
  left_distrib a b c := by
    ext k
    show (R.grMulC a.coeff (fun k => b.coeff k + c.coeff k)) k =
         (R.grMulC a.coeff b.coeff) k + (R.grMulC a.coeff c.coeff) k
    rw [R.grMulC_left_distrib]
  right_distrib a b c := by
    ext k
    show (R.grMulC (fun k => a.coeff k + b.coeff k) c.coeff) k =
         (R.grMulC a.coeff c.coeff) k + (R.grMulC b.coeff c.coeff) k
    rw [R.grMulC_right_distrib]
  zero_mul a := by
    ext k
    show (R.grMulC (fun _ => 0) a.coeff) k = 0
    rw [R.grZeroC_mul]
  mul_zero a := by
    ext k
    show (R.grMulC a.coeff (fun _ => 0)) k = 0
    rw [R.grMulC_zero]
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
  natCast := fun m => ⟨fun k => if k = R.unit then (m : ℂ) else 0⟩
  natCast_zero := by ext k; simp
  natCast_succ m := by
    ext k; show (if k = R.unit then (↑(m + 1) : ℂ) else 0) =
      (if k = R.unit then (m : ℂ) else 0) + (if k = R.unit then 1 else 0)
    split <;> simp
  intCast := fun m => ⟨fun k => if k = R.unit then (m : ℂ) else 0⟩
  intCast_ofNat m := by
    ext k
    show (if k = R.unit then (Int.ofNat m : ℂ) else 0) =
         (if k = R.unit then (m : ℂ) else 0)
    simp [Int.cast_natCast]
  intCast_negSucc m := by
    ext k
    show (if k = R.unit then (Int.negSucc m : ℂ) else 0) =
         -(if k = R.unit then ((m + 1 : ℕ) : ℂ) else 0)
    split
    · simp [Int.negSucc_eq]
    · simp

end GrRingOfC
end
end FusionRing
