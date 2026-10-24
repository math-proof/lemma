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
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.CompleteVarieties
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.CompleteVarieties
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.RationalLineCriterion
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.ProjectiveComplete
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.RationalLineCriterion
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.ProjectiveComplete

universe u

class IsProjectiveVariety (k : outParam (Type u)) [Field k] (V : Type u) [TopologicalSpace V] :
    Prop where
  exists_algVariety_projective :
    ∃ (_ : IsAlgClosed k)
      (algV : AlgebraicGeometry.CompletenessValuationCriterion.AlgVariety k)
      (hcarrier : algV.carrier = V),
      (hcarrier ▸ algV.topInst = ‹TopologicalSpace V›) ∧
      Nonempty (AlgebraicGeometry.CompletenessValuationCriterion.IsProjectiveVariety algV)


def AlgebraicGeometry.CompletenessValuationCriterion.IsMorphismOfVarieties
    {k : Type u} [Field k]
    (X Y : AlgebraicGeometry.CompletenessValuationCriterion.AlgVariety k)
    (f : X.carrier → Y.carrier) : Prop :=
  ∃ (pullback : Y.functionField →+* X.functionField),


    (∀ a : k, pullback (Y.baseEmbed a) = X.baseEmbed a) ∧


    (∀ (P : X.carrier) (r : Y.functionField),
      r ∈ Y.localRingAt (f P) → pullback r ∈ X.localRingAt P)

class IsAlgebraicGroup (k : outParam (Type u)) [Field k] (V : Type u) [TopologicalSpace V] [Group V] : Prop where
  toIsTopologicalGroup : IsTopologicalGroup V
  isVariety :
    ∃ (algV : AlgebraicGeometry.CompletenessValuationCriterion.AlgVariety k)
      (hcarrier : algV.carrier = V),
      (hcarrier ▸ algV.topInst = ‹TopologicalSpace V›)
  mul_isMorphism :
    ∃ (algV : AlgebraicGeometry.CompletenessValuationCriterion.AlgVariety k)
      (algVV : AlgebraicGeometry.CompletenessValuationCriterion.AlgVariety k)
      (hV : algV.carrier = V) (hVV : algVV.carrier = (V × V))
      (f : algVV.carrier → algV.carrier),

      (∀ p : algVV.carrier, cast hV (f p) =
        (cast hVV p).1 * (cast hVV p).2) ∧

      AlgebraicGeometry.CompletenessValuationCriterion.IsMorphismOfVarieties algVV algV f
  inv_isMorphism :
    ∃ (algV : AlgebraicGeometry.CompletenessValuationCriterion.AlgVariety k)
      (hV : algV.carrier = V)
      (f : algV.carrier → algV.carrier),

      (∀ v : algV.carrier, cast hV (f v) = (cast hV v)⁻¹) ∧

      AlgebraicGeometry.CompletenessValuationCriterion.IsMorphismOfVarieties algV algV f


attribute [instance] IsAlgebraicGroup.toIsTopologicalGroup

theorem IsProjectiveVariety.complete (k : Type u) [Field k] (V : Type u) [TopologicalSpace V]
    [h : IsProjectiveVariety k V] : IsCompleteVariety V := by
  obtain ⟨hac, algV, hcarrier, htop, ⟨hproj⟩⟩ := h.exists_algVariety_projective
  subst hcarrier
  have : ‹TopologicalSpace algV.carrier› = algV.topInst := htop.symm
  subst this
  exact AlgebraicGeometry.CompletenessValuationCriterion.projective_variety_isComplete algV hproj

instance IsProjectiveVariety.toIsCompleteVariety
    {k : Type u} [Field k] {V : Type u} [TopologicalSpace V] [IsProjectiveVariety k V] :
    IsCompleteVariety V :=
  IsProjectiveVariety.complete k V

class IsAbelianVariety (k : outParam (Type u)) [Field k] (A : Type u) [TopologicalSpace A] [Group A] : Prop
    extends IsProjectiveVariety k A, IsAlgebraicGroup k A, ConnectedSpace A


open WeierstrassCurve

abbrev WeierstrassEquation (k : Type*) := WeierstrassCurve k

def WeierstrassCurve.shortWeierstrass {R : Type*} [CommRing R] (A B : R) : WeierstrassCurve R :=
  ⟨0, 0, 0, A, B⟩

namespace WeierstrassCurve

abbrev IsShortWeierstrass {R : Type*} [CommRing R] (W : WeierstrassCurve R) : Prop :=
  W.IsShortNF

variable {R : Type*} [CommRing R] (A B : R)

instance shortWeierstrass_isShortNF : (shortWeierstrass A B).IsShortNF where
  a₁ := rfl
  a₂ := rfl
  a₃ := rfl

abbrev EllipticCurve' (k : Type*) [CommRing k] := { W : WeierstrassCurve k // W.IsElliptic }

section Theorem_23_16

namespace WeierstrassCurve.Affine.Point

variable {F : Type*} [Field F] {W : WeierstrassCurve.Affine F} [DecidableEq F]

def MazurCyclicOrders : Finset ℕ := {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12}

def MazurProductOrders : Finset ℕ := {1, 2, 3, 4}

namespace WeierstrassCurve.Affine.Point

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : WeierstrassCurve.Affine F} [DecidableEq F]

def lineThirdIntersection : W.Point → W.Point → W.Point
  | zero, Q => -Q
  | some x₁ y₁ h₁, zero => -(some x₁ y₁ h₁)
  | some x₁ y₁ h₁, some x₂ y₂ h₂ =>
      if hxy : x₁ = x₂ ∧ y₁ = W.negY x₂ y₂ then 0
      else some _ _ (nonsingular_negAdd h₁ h₂ hxy)

abbrev multiplicationByN (n : ℕ) : G →+ G := nsmulAddMonoidHom n

def nTorsionSubgroup (n : ℕ) : AddSubgroup G := (nsmulAddMonoidHom n : G →+ G).ker

abbrev nTorsion (n : ℕ) : AddSubgroup W.Point := nTorsionSubgroup n


end WeierstrassCurve.Affine.Point

namespace WeierstrassCurve

noncomputable def autGroup (R : Type*) [CommRing R] (W : WeierstrassCurve R) :
    Subgroup (VariableChange R) :=
  MulAction.stabilizer (VariableChange R) W

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

instance autGroup_finite (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Finite (autGroup F W) := by
  haveI : Finite (rootsOfUnity 12 F) := Finite.of_fintype _
  let f : autGroup F W → rootsOfUnity 12 F := fun C =>
    ⟨(C : VariableChange F).u,
     (mem_rootsOfUnity 12 _).mpr (autGroup_u_pow_twelve C.2 h2 h3)⟩
  apply Finite.of_injective f
  intro ⟨C₁, hC₁⟩ ⟨C₂, hC₂⟩ h
  have hu : C₁.u = C₂.u := congr_arg Subtype.val h
  exact Subtype.ext (VariableChange.ext hu
    (by rw [aut_r_eq_zero hC₁ h2 h3, aut_r_eq_zero hC₂ h2 h3])
    (by rw [aut_s_eq_zero hC₁ h2, aut_s_eq_zero hC₂ h2])
    (by rw [aut_t_eq_zero hC₁ h2 h3, aut_t_eq_zero hC₂ h2 h3]))

omit [W.IsElliptic] in
noncomputable def autGroupToFHom
    (_h2 : (2 : F) ≠ 0) (_h3 : (3 : F) ≠ 0) : autGroup F W →* F where
  toFun C := ↑(C : VariableChange F).u
  map_one' := by simp [VariableChange.one_def]
  map_mul' _ _ := by simp [VariableChange.mul_def]

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

omit [W.IsElliptic] in
noncomputable def autGroupEquivRootsOfUnity4
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (ha4 : W.a₄ ≠ 0) (ha6 : W.a₆ = 0) :
    autGroup F W ≃ rootsOfUnity 4 F :=
  Equiv.ofBijective
    (fun ⟨C, hC⟩ =>
      ⟨C.u, (mem_rootsOfUnity 4 C.u).mpr
        (autGroup_u_pow4_eq_one_of_j_1728 h2 h3 ha4 hC).1⟩)
    ⟨fun ⟨C₁, hC₁⟩ ⟨C₂, hC₂⟩ h => by
      have hu := congr_arg Subtype.val h
      simp only at hu
      have hd := autGroup_u_pow4_eq_one_of_j_1728 h2 h3 ha4 hC₁
      have hd2 := autGroup_u_pow4_eq_one_of_j_1728 h2 h3 ha4 hC₂
      exact Subtype.ext (VariableChange.ext hu
        (hd.2.1.trans hd2.2.1.symm)
        (hd.2.2.1.trans hd2.2.2.1.symm)
        (hd.2.2.2.trans hd2.2.2.2.symm)),
    fun ⟨ζ, hζ⟩ => by
      refine ⟨⟨⟨ζ, 0, 0, 0⟩, fourth_root_mem_autGroup ((mem_rootsOfUnity 4 ζ).mp hζ) ha6⟩, ?_⟩
      exact Subtype.ext rfl⟩

omit [W.IsElliptic] in
noncomputable def autGroupEquivRootsOfUnity6
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (ha6 : W.a₆ ≠ 0) (ha4 : W.a₄ = 0) :
    autGroup F W ≃ rootsOfUnity 6 F :=
  Equiv.ofBijective
    (fun ⟨C, hC⟩ =>
      ⟨C.u, (mem_rootsOfUnity 6 C.u).mpr
        (autGroup_u_pow6_eq_one_of_j_0 h2 h3 ha6 hC).1⟩)
    ⟨fun ⟨C₁, hC₁⟩ ⟨C₂, hC₂⟩ h => by
      have hu := congr_arg Subtype.val h
      simp only at hu
      have hd := autGroup_u_pow6_eq_one_of_j_0 h2 h3 ha6 hC₁
      have hd2 := autGroup_u_pow6_eq_one_of_j_0 h2 h3 ha6 hC₂
      exact Subtype.ext (VariableChange.ext hu
        (hd.2.1.trans hd2.2.1.symm)
        (hd.2.2.1.trans hd2.2.2.1.symm)
        (hd.2.2.2.trans hd2.2.2.2.symm)),
    fun ⟨ζ, hζ⟩ => by
      refine ⟨⟨⟨ζ, 0, 0, 0⟩, sixth_root_mem_autGroup ((mem_rootsOfUnity 6 ζ).mp hζ) ha4⟩, ?_⟩
      exact Subtype.ext rfl⟩

def ArithmeticGeometry.SmoothProjectiveCurve.genus {k : Type*} [Field k]
    (C : SmoothProjectiveCurve k) : ℕ := C.genusVal

def ArithmeticGeometry.SmoothProjectiveCurve.HasRationalPoint {k : Type*} [Field k]
    (C : SmoothProjectiveCurve k) : Prop :=
  Nonempty C.RatPoint


end Theorem_23_1
