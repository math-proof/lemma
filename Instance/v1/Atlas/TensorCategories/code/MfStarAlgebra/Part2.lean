/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MfStarAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.TensorCategories.code.StarAlgebra
import Lemma.Category.Atlas.v1.TensorCategories.code.StarAlgebra
import Lemma.Category.Atlas.v1.TensorCategories.code.BasedRings
import Abbrev.v1.Atlas.TensorCategories.code.BasedRings
import Mathlib.LinearAlgebra.Dimension.Finrank
import Theorem.v1.Atlas.TensorCategories.code.MfStarAlgebra
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

open Finset Complex


namespace MultifusionRingDef

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : MultifusionRingDef ι)

noncomputable section

namespace MfGrRingOfC

variable {ι : Type*} [DecidableEq ι] [Fintype ι] {R : MultifusionRingDef ι}

/-- The complexified Grothendieck ring of a multifusion ring is a (noncommutative) ring. -/
noncomputable instance instRing : Ring (MfGrRingOfC R) where
  add_assoc a b c := by ext k; simp [add_assoc]
  zero_add a := by ext k; simp
  add_zero a := by ext k; simp
  nsmul := fun n a => ⟨fun k => n • a.coeff k⟩
  nsmul_zero a := by ext k; simp
  nsmul_succ n a := by ext k; simp [add_mul, add_comm]
  add_comm a b := by ext k; simp [add_comm]
  mul_assoc a b c := by
    ext k
    show (R.mfGrMulC (R.mfGrMulC a.coeff b.coeff) c.coeff) k =
         (R.mfGrMulC a.coeff (R.mfGrMulC b.coeff c.coeff)) k
    rw [R.mfGrMulC_assoc]
  one_mul a := by
    ext k
    show (R.mfGrMulC R.mfOneC a.coeff) k = a.coeff k
    rw [R.mfGrMulC_one_left]
  mul_one a := by
    ext k
    show (R.mfGrMulC a.coeff R.mfOneC) k = a.coeff k
    rw [R.mfGrMulC_one_right]
  left_distrib a b c := by
    ext k
    show (R.mfGrMulC a.coeff (fun k => b.coeff k + c.coeff k)) k =
         (R.mfGrMulC a.coeff b.coeff) k + (R.mfGrMulC a.coeff c.coeff) k
    rw [R.mfGrMulC_left_distrib]
  right_distrib a b c := by
    ext k
    show (R.mfGrMulC (fun k => a.coeff k + b.coeff k) c.coeff) k =
         (R.mfGrMulC a.coeff c.coeff) k + (R.mfGrMulC b.coeff c.coeff) k
    rw [R.mfGrMulC_right_distrib]
  zero_mul a := by
    ext k
    show (R.mfGrMulC (fun _ => 0) a.coeff) k = 0
    rw [R.mfZeroC_mul]
  mul_zero a := by
    ext k
    show (R.mfGrMulC a.coeff (fun _ => 0)) k = 0
    rw [R.mfGrMulC_zero]
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
  natCast := fun m => ⟨fun k => if k ∈ R.I₀ then (m : ℂ) else 0⟩
  natCast_zero := by ext k; simp
  natCast_succ m := by
    ext k; show (if k ∈ R.I₀ then (↑(m + 1) : ℂ) else 0) =
      (if k ∈ R.I₀ then (m : ℂ) else 0) + (if k ∈ R.I₀ then 1 else 0)
    split <;> simp
  intCast := fun m => ⟨fun k => if k ∈ R.I₀ then (m : ℂ) else 0⟩
  intCast_ofNat m := by
    ext k
    show (if k ∈ R.I₀ then (Int.ofNat m : ℂ) else 0) =
         (if k ∈ R.I₀ then (m : ℂ) else 0)
    simp [Int.cast_natCast]
  intCast_negSucc m := by
    ext k
    show (if k ∈ R.I₀ then (Int.negSucc m : ℂ) else 0) =
         -(if k ∈ R.I₀ then ((m + 1 : ℕ) : ℂ) else 0)
    split
    · simp [Int.negSucc_eq]
    · simp

end MfGrRingOfC
end
end MultifusionRingDef
