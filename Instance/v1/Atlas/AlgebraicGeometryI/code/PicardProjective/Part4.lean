/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PicardProjective.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.UniqueFactorizationDomain.ClassGroup
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Theorem.v1.Atlas.AlgebraicGeometryI.code.PicardProjective.Part5


noncomputable section

namespace PicardProjective

open MvPolynomial


/-- The graded Picard group is an additive commutative group. -/
instance gradedPicardGroupAddCommGroup (σ : Type*) (k : Type*) [Field k] :
    AddCommGroup (GradedPicardGroup σ k) where
  add_assoc a b c := by
    induction a using Quotient.ind
    induction b using Quotient.ind
    induction c using Quotient.ind
    apply Quotient.sound
    apply ring_assoc_equiv <;> simp [HomogFraction.mul, mul_assoc, Nat.add_assoc]
  zero_add a := by
    induction a using Quotient.ind
    apply Quotient.sound
    apply ring_assoc_equiv <;> simp [HomogFraction.mul, HomogFraction.one]
  add_zero a := by
    induction a using Quotient.ind
    apply Quotient.sound
    apply ring_assoc_equiv <;> simp [HomogFraction.mul, HomogFraction.one]
  neg_add_cancel a := by
    induction a using Quotient.ind
    rename_i p
    apply Quotient.sound
    refine ⟨1, 1, 0, 0, one_ne_zero, one_ne_zero,
      isHomogeneous_one σ k, isHomogeneous_one σ k, rfl, ?_⟩
    simp only [HomogFraction.mul, HomogFraction.inv, HomogFraction.one]
    have h : p.den * p.num * 1 * 1 = 1 * 1 * (p.num * p.den) := by ring
    rw [h]
  add_comm a b := by
    induction a using Quotient.ind
    induction b using Quotient.ind
    apply Quotient.sound
    apply ring_assoc_equiv <;> simp [HomogFraction.mul, mul_comm, Nat.add_comm]
  nsmul := nsmulRec
  zsmul := zsmulRec


end PicardProjective
end
