/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SyzygiesKoszul.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.Algebra.Module.GradedModule
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Instance.v1.Atlas.LieGroups.code.SyzygiesKoszul


noncomputable section

set_option synthInstance.maxHeartbeats 80000

open MvPolynomial

variable (k : Type*) [Field k] (n : ℕ)

local notation "R" => MvPolynomial (Fin n) k

noncomputable def freeModuleGradingEquiv (m d : ℕ) :
    freeModuleGrading k n (m := m) d ≃ₗ[k]
    (Fin m → ↥(homogeneousSubmodule (Fin n) k d)) where
  toFun f i := ⟨f.val i, f.property i⟩
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl
  invFun g := ⟨fun i => (g i).val, fun i => (g i).property⟩
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl

def koszulProjL (b c : ℕ) : (Fin (b + c) → A) →ₗ[A] (Fin b → A) where
  toFun v i := v (Fin.castAdd c i); map_add' _ _ := rfl; map_smul' _ _ := rfl

def koszulProjR (b c : ℕ) : (Fin (b + c) → A) →ₗ[A] (Fin c → A) where
  toFun v i := v (Fin.natAdd b i); map_add' _ _ := rfl; map_smul' _ _ := rfl

def koszulReindex {a b : ℕ} (h : a = b) : (Fin a → A) →ₗ[A] (Fin b → A) where
  toFun v i := v (Fin.cast h.symm i); map_add' _ _ := rfl; map_smul' _ _ := rfl

def koszulSmulLM (a_val : A) (k : ℕ) : (Fin k → A) →ₗ[A] (Fin k → A) where
  toFun v i := a_val * v i
  map_add' v w := by ext; simp [mul_add]
  map_smul' r v := by ext; simp [smul_eq_mul, mul_left_comm]

def koszulInjectL (b c : ℕ) : (Fin b → A) →ₗ[A] (Fin (b + c) → A) where
  toFun u := Fin.addCases u (fun _ => 0)
  map_add' u₁ u₂ := by ext ⟨i, hi⟩; by_cases h : i < b <;> simp [Fin.addCases, h]
  map_smul' r u := by ext ⟨i, hi⟩; by_cases h : i < b <;> simp [Fin.addCases, h, smul_eq_mul]

def koszulInjectR (b c : ℕ) : (Fin c → A) →ₗ[A] (Fin (b + c) → A) where
  toFun w := Fin.addCases (fun _ => 0) w
  map_add' w₁ w₂ := by ext ⟨i, hi⟩; by_cases h : i < b <;> simp [Fin.addCases, h]
  map_smul' r w := by ext ⟨i, hi⟩; by_cases h : i < b <;> simp [Fin.addCases, h, smul_eq_mul]

noncomputable def koszulDSafe (n : ℕ)
    (d' : ∀ i, i < n → (Fin (n.choose (i+1)) → A) →ₗ[A] (Fin (n.choose i) → A))
    (p : ℕ) : (Fin (n.choose (p+1)) → A) →ₗ[A] (Fin (n.choose p) → A) :=
  if h : p < n then d' p h else 0

end KoszulHelpers

section KoszulConeDiff

variable {A : Type*} [CommRing A]

noncomputable def koszulConeDiff0 (n : ℕ) (hn : 0 < n)
    (d' : ∀ i, i < n → (Fin (n.choose (i+1)) → A) →ₗ[A] (Fin (n.choose i) → A))
    (a : A) : (Fin ((n+1).choose 1) → A) →ₗ[A] (Fin ((n+1).choose 0) → A) :=
  let h_s := Nat.choose_succ_succ n 0
  have h_t : n.choose 0 = (n+1).choose 0 := by simp [Nat.choose_zero_right]
  (koszulReindex h_t).comp (
    (-(koszulSmulLM a (n.choose 0))).comp ((koszulProjL (n.choose 0) (n.choose 1)).comp (koszulReindex h_s)) +
    (d' 0 hn).comp ((koszulProjR (n.choose 0) (n.choose 1)).comp (koszulReindex h_s)))

noncomputable def koszulConeDiffSucc (n p' : ℕ) (hp' : p' < n)
    (d' : ∀ i, i < n → (Fin (n.choose (i+1)) → A) →ₗ[A] (Fin (n.choose i) → A))
    (a : A) : (Fin ((n+1).choose (p'+2)) → A) →ₗ[A] (Fin ((n+1).choose (p'+1)) → A) :=
  (koszulReindex (Nat.choose_succ_succ n p').symm).comp (
    (koszulInjectL (n.choose p') (n.choose (p'+1))).comp
      ((d' p' hp').comp ((koszulProjL (n.choose (p'+1)) (n.choose (p'+2))).comp
        (koszulReindex (Nat.choose_succ_succ n (p'+1))))) +
    (koszulInjectR (n.choose p') (n.choose (p'+1))).comp (
      (koszulSmulLM ((-1 : A) ^ (p' + 2) * a) (n.choose (p'+1))).comp
        ((koszulProjL (n.choose (p'+1)) (n.choose (p'+2))).comp
          (koszulReindex (Nat.choose_succ_succ n (p'+1)))) +
      (koszulDSafe n d' (p'+1)).comp
        ((koszulProjR (n.choose (p'+1)) (n.choose (p'+2))).comp
          (koszulReindex (Nat.choose_succ_succ n (p'+1))))))

noncomputable def koszulConeDiff (n : ℕ) (hn : 0 < n)
    (d' : ∀ i, i < n → (Fin (n.choose (i+1)) → A) →ₗ[A] (Fin (n.choose i) → A))
    (a : A) : (p : ℕ) → (hp : p < n + 1) →
    (Fin ((n+1).choose (p+1)) → A) →ₗ[A] (Fin ((n+1).choose p) → A)
  | 0, _ => koszulConeDiff0 n hn d' a
  | p + 1, hp => koszulConeDiffSucc n p (Nat.lt_of_succ_lt_succ hp) d' a

end KoszulConeDiff

section KoszulBlockLemmas

variable {A : Type*} [CommRing A]

end KoszulBlockLemmas

section KoszulConeExactness

omit k n

end KoszulConeExactness

def quotientHomogeneousSubmodule
    (I : Ideal (MvPolynomial (Fin n) k)) (i : ℕ) :
    Submodule k (MvPolynomial (Fin n) k ⧸ I) :=
  (homogeneousSubmodule (Fin n) k i).map (I.mkQ.restrictScalars k)

def qAnalog (d : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk (fun i => if i < d then 1 else 0)

def invOneSubX : PowerSeries ℤ :=
  PowerSeries.mk (fun _ => 1)

