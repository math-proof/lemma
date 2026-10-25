/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalFunctorsCohomology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.TensorCategories.code.GradedVec.Part6
import Lemma.Category.Atlas.v1.TensorCategories.code.GradedVec
import Mathlib.GroupTheory.GroupAction.Basic
import Def.v1.Atlas.TensorCategories.code.MonoidalFunctorsCohomology
set_option maxHeartbeats 800000

open CategoryTheory

universe u v


section CommGroupLemmas

variable {A : Type*} [CommGroup A]

/-- Rearrangement lemma: `a * b * c * d⁻¹ * e⁻¹ = 1` is equivalent to `e * d = a * b * c`
in a commutative group. -/
lemma prod5_eq_one_iff {a b c d e : A} :
    a * b * c * d⁻¹ * e⁻¹ = 1 ↔ e * d = a * b * c := by
  rw [eq_comm (a := e * d)]
  show a * b * c * d⁻¹ * e⁻¹ = 1 ↔ a * b * c = e * d
  rw [show (a * b * c * d⁻¹ * e⁻¹ : A) = a * b * c / (e * d) from by
    simp [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm]]
  exact div_eq_one

/-- `d¹` of the pointwise inverse of a 1-cochain is the pointwise inverse of `d¹`. -/
lemma d1_inv (η : Cochain1 G A) (g h : G) :
    d1 G A (fun x => (η x)⁻¹) g h = (d1 G A η g h)⁻¹ := by
  simp [d1, mul_inv_rev, mul_comm, inv_inv]

/-- `d²` of the pointwise inverse of a 2-cochain is the pointwise inverse of `d²`. -/
lemma d2_inv (μ : Cochain2 G A) (g h l : G) :
    d2 G A (fun x y => (μ x y)⁻¹) g h l = (d2 G A μ g h l)⁻¹ := by
  simp [d2, mul_inv_rev, mul_comm, mul_left_comm, inv_inv, mul_assoc]

end CommGroupLemmas
