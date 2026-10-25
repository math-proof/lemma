/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HeckeKL.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Def.v1.Atlas.LieGroups.code.CompositionSeries
import Lemma.Int.StandardFiltrationMultiplicity.eq.DimHomProjectiveContragredientVerma
import Theorem.v1.Atlas.LieGroups.code.HeckeKL


noncomputable section

open Polynomial

attribute [instance] CoxeterGroupData.grpInst CoxeterGroupData.finInst
  CoxeterGroupData.decEq

instance HeckeAlgebra.instRing (C : CoxeterGroupData) : Ring (HeckeAlgebra C) where
  __ := HeckeAlgebra.instAddCommGroup C
  mul := heckeMul C
  one := Finsupp.single 1 1
  mul_assoc := by
    intro a b c
    show heckeMul C (heckeMul C a b) c = heckeMul C a (heckeMul C b c)

    have hzl : ∀ (g : HeckeAlgebra C), heckeMul C 0 g = 0 :=
      fun _ => Finsupp.sum_zero_index
    have hzr : ∀ (f : HeckeAlgebra C), heckeMul C f 0 = 0 := by
      intro f; unfold heckeMul
      have : ∀ (w₁ : C.W) (a₁ : HeckeCoeffRing),
        Finsupp.sum (0 : HeckeAlgebra C) (fun w₂ a₂ => (a₁ * a₂) • heckeMulBasis C w₁ w₂) = 0 :=
        fun _ _ => Finsupp.sum_zero_index
      conv_lhs => arg 2; ext w₁ a₁; rw [this w₁ a₁]
      simp [Finsupp.sum]
    have hal : ∀ (f g h : HeckeAlgebra C),
        heckeMul C (f + g) h = heckeMul C f h + heckeMul C g h := by
      intro f g h; unfold heckeMul
      apply Finsupp.sum_add_index'
      · intro i; show h.sum (fun w₂ a₂ => (0 * a₂) • heckeMulBasis C i w₂) = 0
        simp [zero_mul, zero_smul, Finsupp.sum]
      · intro i b₁ b₂
        conv_lhs => arg 2; ext w₂ a₂; rw [add_mul, add_smul]
        rw [← Finsupp.sum_add]
    have har : ∀ (f g h : HeckeAlgebra C),
        heckeMul C f (g + h) = heckeMul C f g + heckeMul C f h := by
      intro f g h; unfold heckeMul
      have inner_split : ∀ w₁ a₁,
        (g + h).sum (fun w₂ a₂ => (a₁ * a₂) • heckeMulBasis C w₁ w₂) =
        g.sum (fun w₂ a₂ => (a₁ * a₂) • heckeMulBasis C w₁ w₂) +
        h.sum (fun w₂ a₂ => (a₁ * a₂) • heckeMulBasis C w₁ w₂) := by
        intro w₁ a₁
        apply Finsupp.sum_add_index'
        · intro i; simp
        · intro i b₁ b₂; rw [mul_add, add_smul]
      conv_lhs => arg 2; ext w₁ a₁; rw [inner_split w₁ a₁]
      rw [← Finsupp.sum_add]

    apply @Finsupp.induction_linear C.W HeckeCoeffRing _
      (fun a => heckeMul C (heckeMul C a b) c = heckeMul C a (heckeMul C b c)) a
    ·
      rw [hzl, hzl, hzl]
    ·
      intro a₁ a₂ h₁ h₂
      rw [hal, hal, h₁, h₂, ← hal]
    ·
      intro w₁ r₁
      apply @Finsupp.induction_linear C.W HeckeCoeffRing _
        (fun b => heckeMul C (heckeMul C (Finsupp.single w₁ r₁) b) c =
                  heckeMul C (Finsupp.single w₁ r₁) (heckeMul C b c)) b
      ·
        rw [hzr, hzl, hzr]
      ·
        intro b₁ b₂ h₁ h₂
        rw [har, hal, h₁, h₂, ← har]; congr 1; rw [← hal]
      ·
        intro w₂ r₂
        apply @Finsupp.induction_linear C.W HeckeCoeffRing _
          (fun c => heckeMul C (heckeMul C (Finsupp.single w₁ r₁) (Finsupp.single w₂ r₂)) c =
                    heckeMul C (Finsupp.single w₁ r₁) (heckeMul C (Finsupp.single w₂ r₂) c)) c
        ·
          rw [hzr, hzr, hzr]
        ·
          intro c₁ c₂ h₁ h₂
          rw [har, h₁, har, h₂, ← har]
        ·
          intro w₃ r₃


          have hss12 : heckeMul C (Finsupp.single w₁ r₁) (Finsupp.single w₂ r₂) =
              (r₁ * r₂) • heckeMulBasis C w₁ w₂ := by
            unfold heckeMul
            rw [Finsupp.sum_single_index (by simp [zero_mul, zero_smul, Finsupp.sum])]
            rw [Finsupp.sum_single_index (by simp [mul_zero, zero_smul])]
          have hss23 : heckeMul C (Finsupp.single w₂ r₂) (Finsupp.single w₃ r₃) =
              (r₂ * r₃) • heckeMulBasis C w₂ w₃ := by
            unfold heckeMul
            rw [Finsupp.sum_single_index (by simp [zero_mul, zero_smul, Finsupp.sum])]
            rw [Finsupp.sum_single_index (by simp [mul_zero, zero_smul])]
          rw [hss12, hss23]


          show heckeMul C ((r₁ * r₂) • heckeMulBasis C w₁ w₂) (Finsupp.single w₃ r₃) =
               heckeMul C (Finsupp.single w₁ r₁) ((r₂ * r₃) • heckeMulBasis C w₂ w₃)

          have hml : ∀ (f : HeckeAlgebra C) (w : C.W) (r : HeckeCoeffRing),
              heckeMul C f (Finsupp.single w r) =
              f.sum (fun v d => (d * r) • heckeMulBasis C v w) := by
            intro f w r; unfold heckeMul; congr 1; ext v d
            rw [Finsupp.sum_single_index (by simp [mul_zero, zero_smul])]

          have hmr : ∀ (w : C.W) (r : HeckeCoeffRing) (g : HeckeAlgebra C),
              heckeMul C (Finsupp.single w r) g =
              g.sum (fun v d => (r * d) • heckeMulBasis C w v) := by
            intro w r g; unfold heckeMul
            rw [Finsupp.sum_single_index (by simp [zero_mul, zero_smul, Finsupp.sum])]

          rw [hml, hmr]


          have key : ∀ (b : HeckeCoeffRing) (g : HeckeAlgebra C)
              (h : C.W → HeckeCoeffRing → HeckeAlgebra C) (h0 : ∀ i, h i 0 = 0),
              (b • g).sum h = g.sum (fun i cc => h i (b • cc)) :=
            fun b g h h0 => Finsupp.sum_smul_index' h0
          rw [key (r₁ * r₂) (heckeMulBasis C w₁ w₂)
              (fun v d => (d * r₃) • heckeMulBasis C v w₃)
              (fun i => by simp [zero_mul, zero_smul])]
          rw [key (r₂ * r₃) (heckeMulBasis C w₂ w₃)
              (fun v d => (r₁ * d) • heckeMulBasis C w₁ v)
              (fun i => by simp [mul_zero, zero_smul])]

          simp_rw [smul_eq_mul]

          conv_lhs => arg 2; ext v d; rw [show (r₁ * r₂) * d * r₃ = (r₁ * r₂ * r₃) * d by ring, mul_smul]
          conv_rhs => arg 2; ext v d; rw [show r₁ * ((r₂ * r₃) * d) = (r₁ * r₂ * r₃) * d by ring, mul_smul]
          rw [← Finsupp.smul_sum, ← Finsupp.smul_sum]
          congr 1
          exact heckeMulBasis_assoc C w₁ w₂ w₃

  one_mul := by
    intro b
    show heckeMul C (Finsupp.single 1 1) b = b
    unfold heckeMul
    rw [Finsupp.sum_single_index]
    · have key : (fun w₂ a₂ => (1 * a₂) • heckeMulBasis C 1 w₂) =
                 (fun w₂ (a₂ : HeckeCoeffRing) => (Finsupp.single w₂ a₂ : HeckeAlgebra C)) := by
        ext w₂ a₂ : 2
        simp only [one_mul]
        have hb : heckeMulBasis C 1 w₂ = Finsupp.single w₂ 1 :=
          heckeMulBasis_one_left C w₂
        rw [hb]
        change (a₂ • (Finsupp.single w₂ 1 : C.W →₀ HeckeCoeffRing) : C.W →₀ HeckeCoeffRing) =
               (Finsupp.single w₂ a₂ : C.W →₀ HeckeCoeffRing)
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [key]
      exact Finsupp.sum_single _
    · simp [zero_mul, zero_smul, Finsupp.sum]
  mul_one := by
    intro b
    show heckeMul C b (Finsupp.single 1 1) = b
    unfold heckeMul
    have inner_simp : ∀ w₁ (a₁ : HeckeCoeffRing),
      (Finsupp.single (1 : C.W) (1 : HeckeCoeffRing)).sum
        (fun w₂ a₂ => (a₁ * a₂) • heckeMulBasis C w₁ w₂) =
      Finsupp.single w₁ a₁ := by
      intro w₁ a₁
      rw [Finsupp.sum_single_index]
      · rw [mul_one]
        have hb : heckeMulBasis C w₁ 1 = Finsupp.single w₁ 1 :=
          heckeMulBasis_one_right C w₁
        rw [hb]
        change (a₁ • (Finsupp.single w₁ 1 : C.W →₀ HeckeCoeffRing) : C.W →₀ HeckeCoeffRing) =
               (Finsupp.single w₁ a₁ : C.W →₀ HeckeCoeffRing)
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      · simp [mul_zero, zero_smul]
    have key : (fun w₁ a₁ =>
      (Finsupp.single (1 : C.W) (1 : HeckeCoeffRing)).sum
        (fun w₂ a₂ => (a₁ * a₂) • heckeMulBasis C w₁ w₂)) =
      (fun w₁ (a₁ : HeckeCoeffRing) => (Finsupp.single w₁ a₁ : HeckeAlgebra C)) := by
      ext w₁ a₁ : 2
      exact inner_simp w₁ a₁
    rw [key]
    exact Finsupp.sum_single _
  left_distrib := by
    intro f g h
    show heckeMul C f (g + h) = heckeMul C f g + heckeMul C f h
    unfold heckeMul
    have inner_split : ∀ w₁ a₁,
      (g + h).sum (fun w₂ a₂ => (a₁ * a₂) • heckeMulBasis C w₁ w₂) =
      g.sum (fun w₂ a₂ => (a₁ * a₂) • heckeMulBasis C w₁ w₂) +
      h.sum (fun w₂ a₂ => (a₁ * a₂) • heckeMulBasis C w₁ w₂) := by
      intro w₁ a₁
      apply Finsupp.sum_add_index'
      · intro i; simp
      · intro i b₁ b₂; rw [mul_add, add_smul]
    conv_lhs => arg 2; ext w₁ a₁; rw [inner_split w₁ a₁]
    rw [← Finsupp.sum_add]
  right_distrib := by
    intro f g h
    show heckeMul C (f + g) h = heckeMul C f h + heckeMul C g h
    unfold heckeMul
    apply Finsupp.sum_add_index'
    · intro i
      show h.sum (fun w₂ a₂ => (0 * a₂) • heckeMulBasis C i w₂) = 0
      simp [zero_mul, zero_smul, Finsupp.sum]
    · intro i b₁ b₂
      conv_lhs => arg 2; ext w₂ a₂; rw [add_mul, add_smul]
      rw [← Finsupp.sum_add]
  zero_mul := by
    intro g
    show heckeMul C 0 g = 0
    unfold heckeMul
    exact Finsupp.sum_zero_index
  mul_zero := by
    intro f
    show heckeMul C f 0 = 0
    unfold heckeMul
    have : ∀ (w₁ : C.W) (a₁ : HeckeCoeffRing),
      Finsupp.sum (0 : HeckeAlgebra C) (fun w₂ a₂ => (a₁ * a₂) • heckeMulBasis C w₁ w₂) = 0 :=
      fun _ _ => Finsupp.sum_zero_index
    conv_lhs => arg 2; ext w₁ a₁; rw [this w₁ a₁]
    simp [Finsupp.sum]
  natCast n := Finsupp.single 1 (n : HeckeCoeffRing)
  natCast_zero := by
    change Finsupp.single (1 : C.W) ((0 : ℕ) : HeckeCoeffRing) = 0
    simp
  natCast_succ := by
    intro n
    change Finsupp.single (1 : C.W) ((n + 1 : ℕ) : HeckeCoeffRing) =
      Finsupp.single (1 : C.W) ((n : ℕ) : HeckeCoeffRing) + Finsupp.single (1 : C.W) (1 : HeckeCoeffRing)
    rw [← Finsupp.single_add]
    congr 1
    push_cast
    ring
  intCast n := Finsupp.single 1 (n : HeckeCoeffRing)
  intCast_ofNat := by
    intro n
    change Finsupp.single (1 : C.W) ((↑n : ℤ) : HeckeCoeffRing) =
      Finsupp.single (1 : C.W) ((n : ℕ) : HeckeCoeffRing)
    simp [Int.cast_natCast]
  intCast_negSucc := by
    intro n
    change Finsupp.single (1 : C.W) ((Int.negSucc n : ℤ) : HeckeCoeffRing) =
      -Finsupp.single (1 : C.W) ((n + 1 : ℕ) : HeckeCoeffRing)
    ext w
    simp only [Finsupp.single_apply, Finsupp.neg_apply]
    split
    · simp [Int.negSucc_eq, Int.cast_neg, Int.cast_natCast, Nat.cast_succ]
    · simp

end
