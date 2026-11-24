module
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.GroupTheory.Torsion
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
public import Mathlib.LinearAlgebra.Lagrange
public import Instance.v1.Atlas.ArithmeticGeometry.code.CompleteVarieties
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.CompleteVarieties
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.RationalLineCriterion
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.ProjectiveComplete
public import Def.v1.Atlas.ArithmeticGeometry.code.RationalLineCriterion
public import Structure.v1.Atlas.ArithmeticGeometry.code.ProjectiveComplete
public import Def.v1.Atlas.ArithmeticGeometry.code.EllipticCurves.Part6


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
universe u

attribute [instance] IsAlgebraicGroup.toIsTopologicalGroup

open WeierstrassCurve


namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (A B : R)

section Theorem_23_16

namespace WeierstrassCurve.Affine.Point

variable {F : Type*} [Field F] {W : WeierstrassCurve.Affine F} [DecidableEq F]

namespace WeierstrassCurve

section Theorem26_11

variable {F : Type*} [Field F] {W : WeierstrassCurve F} [W.IsShortNF] [W.IsElliptic]

omit [W.IsElliptic] in
theorem autGroup_u_pow4_eq_one_of_j_1728
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (ha4 : W.a₄ ≠ 0)
    {C : VariableChange F} (hC : C ∈ autGroup F W) :
    C.u ^ 4 = 1 ∧ C.r = 0 ∧ C.s = 0 ∧ C.t = 0 :=
  ⟨u_pow_eq_one_of_inv_val_pow_eq_one (aut_u_inv_pow4_eq_one hC h2 h3 ha4),
    aut_r_eq_zero hC h2 h3, aut_s_eq_zero hC h2, aut_t_eq_zero hC h2 h3⟩

omit [W.IsElliptic] in
theorem autGroup_u_pow6_eq_one_of_j_0
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (ha6 : W.a₆ ≠ 0)
    {C : VariableChange F} (hC : C ∈ autGroup F W) :
    C.u ^ 6 = 1 ∧ C.r = 0 ∧ C.s = 0 ∧ C.t = 0 :=
  ⟨u_pow_eq_one_of_inv_val_pow_eq_one (aut_u_inv_pow6_eq_one hC h2 h3 ha6),
    aut_r_eq_zero hC h2 h3, aut_s_eq_zero hC h2, aut_t_eq_zero hC h2 h3⟩

lemma u_inv_val_pow_eq_one {n : ℕ} {u : Fˣ} (h : u ^ n = 1) :
    (↑u⁻¹ : F) ^ n = 1 := by
  rw [Units.val_inv_eq_inv_val, inv_pow, inv_eq_one]
  have := congr_arg Units.val h
  simp only [Units.val_pow_eq_pow_val, Units.val_one] at this
  exact this

omit [W.IsElliptic] in
lemma fourth_root_mem_autGroup {u : Fˣ} (hu : u ^ 4 = 1) (ha₆ : W.a₆ = 0) :
    (⟨u, 0, 0, 0⟩ : VariableChange F) ∈ autGroup F W := by
  show (⟨u, 0, 0, 0⟩ : VariableChange F) • W = W
  rw [variableChange_def]
  have hinv : (↑u⁻¹ : F) ^ 4 = 1 := u_inv_val_pow_eq_one hu
  ext <;> simp only [IsShortNF.a₁ (W := W), IsShortNF.a₂ (W := W),
    IsShortNF.a₃ (W := W), ha₆] <;> ring_nf
  · rw [hinv, one_mul]

omit [W.IsElliptic] in
lemma sixth_root_mem_autGroup {u : Fˣ} (hu : u ^ 6 = 1) (ha₄ : W.a₄ = 0) :
    (⟨u, 0, 0, 0⟩ : VariableChange F) ∈ autGroup F W := by
  show (⟨u, 0, 0, 0⟩ : VariableChange F) • W = W
  rw [variableChange_def]
  have hinv : (↑u⁻¹ : F) ^ 6 = 1 := u_inv_val_pow_eq_one hu
  ext <;> simp only [IsShortNF.a₁ (W := W), IsShortNF.a₂ (W := W),
    IsShortNF.a₃ (W := W), ha₄] <;> ring_nf
  · rw [hinv, one_mul]

end Theorem26_11
end WeierstrassCurve
end WeierstrassCurve.Affine.Point
end Theorem_23_16
end WeierstrassCurve
