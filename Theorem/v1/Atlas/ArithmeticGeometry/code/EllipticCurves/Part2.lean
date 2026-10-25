/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.GroupTheory.Torsion
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.LinearAlgebra.Lagrange
import Instance.v1.Atlas.ArithmeticGeometry.code.CompleteVarieties
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.CompleteVarieties
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.RationalLineCriterion
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.ProjectiveComplete
import Def.v1.Atlas.ArithmeticGeometry.code.RationalLineCriterion
import Structure.v1.Atlas.ArithmeticGeometry.code.ProjectiveComplete
import Def.v1.Atlas.ArithmeticGeometry.code.EllipticCurves.Part5
universe u

attribute [instance] IsAlgebraicGroup.toIsTopologicalGroup

open WeierstrassCurve


namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (A B : R)

section Theorem_23_16

namespace WeierstrassCurve.Affine.Point

variable {F : Type*} [Field F] {W : WeierstrassCurve.Affine F} [DecidableEq F]

namespace WeierstrassCurve

section ShortNFAut

variable {F : Type*} [Field F] {W : WeierstrassCurve F} [W.IsShortNF]

lemma aut_s_eq_zero {C : VariableChange F} (hC : C • W = W) (h2 : (2 : F) ≠ 0) :
    C.s = 0 := by
  have ha1 : (C • W).a₁ = W.a₁ := by rw [hC]
  rw [variableChange_a₁, IsShortNF.a₁ (W := W)] at ha1
  simp only [zero_add] at ha1
  cases mul_eq_zero.mp ha1 with
  | inl h => exact absurd h C.u_inv_ne_zero
  | inr h => exact mul_left_cancel₀ h2 (h.trans (mul_zero 2).symm)

lemma aut_r_eq_zero {C : VariableChange F} (hC : C • W = W)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) : C.r = 0 := by
  have ha2 : (C • W).a₂ = W.a₂ := by rw [hC]
  rw [variableChange_a₂, IsShortNF.a₁ (W := W), IsShortNF.a₂ (W := W)] at ha2
  simp only [aut_s_eq_zero hC h2, mul_zero, sub_zero, sq, zero_add] at ha2
  rcases mul_eq_zero.mp ha2 with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' C.u_inv_ne_zero
    · exact absurd h' C.u_inv_ne_zero
  · exact mul_left_cancel₀ h3 (h.trans (mul_zero 3).symm)

lemma aut_t_eq_zero {C : VariableChange F} (hC : C • W = W)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) : C.t = 0 := by
  have ha3 : (C • W).a₃ = W.a₃ := by rw [hC]
  rw [variableChange_a₃, IsShortNF.a₁ (W := W), IsShortNF.a₃ (W := W)] at ha3
  simp only [aut_r_eq_zero hC h2 h3, zero_mul, zero_add] at ha3
  cases mul_eq_zero.mp ha3 with
  | inl h => exact absurd h (pow_ne_zero 3 C.u_inv_ne_zero)
  | inr h => exact mul_left_cancel₀ h2 (h.trans (mul_zero 2).symm)

lemma aut_u_inv_pow4_eq_one {C : VariableChange F} (hC : C • W = W)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (ha4 : W.a₄ ≠ 0) :
    (↑C.u⁻¹ : F) ^ 4 = 1 := by
  have h := aut_u_inv_pow4_mul_a₄ hC h2 h3
  rwa [← sub_eq_zero, ← sub_one_mul, mul_eq_zero, sub_eq_zero, or_iff_left ha4] at h

lemma aut_u_inv_pow6_eq_one {C : VariableChange F} (hC : C • W = W)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (ha6 : W.a₆ ≠ 0) :
    (↑C.u⁻¹ : F) ^ 6 = 1 := by
  have h := aut_u_inv_pow6_mul_a₆ hC h2 h3
  rwa [← sub_eq_zero, ← sub_one_mul, mul_eq_zero, sub_eq_zero, or_iff_left ha6] at h

lemma u_pow_eq_one_of_inv_val_pow_eq_one {C : VariableChange F} {n : ℕ}
    (h : (↑C.u⁻¹ : F) ^ n = 1) : C.u ^ n = 1 := by
  rw [Units.val_inv_eq_inv_val, inv_pow, inv_eq_one] at h
  exact Units.val_injective (by rw [Units.val_pow_eq_pow_val]; simpa using h)

end ShortNFAut

section Theorem26_11

variable {F : Type*} [Field F] {W : WeierstrassCurve F} [W.IsShortNF] [W.IsElliptic]

lemma autGroup_u_pow_twelve {C : VariableChange F} (hC : C ∈ autGroup F W)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) : C.u ^ 12 = 1 := by
  rcases a₄_ne_zero_or_a₆_ne_zero (W := W) with ha4 | ha6
  · have h4 := u_pow_eq_one_of_inv_val_pow_eq_one (aut_u_inv_pow4_eq_one hC h2 h3 ha4)
    have : C.u ^ 12 = (C.u ^ 4) ^ 3 := by group
    rw [this, h4, one_pow]
  · have h6 := u_pow_eq_one_of_inv_val_pow_eq_one (aut_u_inv_pow6_eq_one hC h2 h3 ha6)
    have : C.u ^ 12 = (C.u ^ 6) ^ 2 := by group
    rw [this, h6, one_pow]

end Theorem26_11
end WeierstrassCurve
end WeierstrassCurve.Affine.Point
end Theorem_23_16
end WeierstrassCurve
