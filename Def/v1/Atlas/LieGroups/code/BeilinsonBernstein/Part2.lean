/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.CategoryTheory.Equivalence
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Adjoin.Basic
import Class.v1.Atlas.LieGroups.code.BeilinsonBernstein
open CategoryTheory


namespace BeilinsonBernstein

noncomputable section

universe u

attribute [instance] CAlgebra.instRing CAlgebra.instAlgebra

attribute [instance] AbCat.instCat

attribute [instance] GradedAlgebra.instRing GradedAlgebra.instAlgebra

noncomputable def AlgHom.liftOfSurjectiveNC {R A B C : Type*}
    [CommSemiring R] [Ring A] [Ring B] [Ring C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    (π : A →ₐ[R] B) (hπ : Function.Surjective π) (f : A →ₐ[R] C)
    (hker : ∀ x, π x = 0 → f x = 0) : B →ₐ[R] C where
  toFun b := f (Function.surjInv hπ b)
  map_one' := by
    have hk : π (Function.surjInv hπ 1 - 1) = 0 := by simp [Function.surjInv_eq]
    have := hker _ hk; rwa [map_sub, map_one, sub_eq_zero] at this
  map_mul' x y := by
    obtain ⟨a, rfl⟩ := hπ x; obtain ⟨b, rfl⟩ := hπ y
    have hab := hker _ (show π (Function.surjInv hπ (π a * π b) - a * b) = 0 by
      rw [← map_mul]; simp [Function.surjInv_eq])
    rw [map_sub, map_mul, sub_eq_zero] at hab
    have ha := hker _ (show π (Function.surjInv hπ (π a) - a) = 0 by
      simp [Function.surjInv_eq])
    rw [map_sub, sub_eq_zero] at ha
    have hb := hker _ (show π (Function.surjInv hπ (π b) - b) = 0 by
      simp [Function.surjInv_eq])
    rw [map_sub, sub_eq_zero] at hb; rw [hab, ha, hb]
  map_zero' := hker _ (by simp [Function.surjInv_eq])
  map_add' x y := by
    obtain ⟨a, rfl⟩ := hπ x; obtain ⟨b, rfl⟩ := hπ y
    have hab := hker _ (show π (Function.surjInv hπ (π a + π b) - (a + b)) = 0 by
      rw [← map_add]; simp [Function.surjInv_eq])
    rw [map_sub, map_add, sub_eq_zero] at hab
    have ha := hker _ (show π (Function.surjInv hπ (π a) - a) = 0 by
      simp [Function.surjInv_eq])
    rw [map_sub, sub_eq_zero] at ha
    have hb := hker _ (show π (Function.surjInv hπ (π b) - b) = 0 by
      simp [Function.surjInv_eq])
    rw [map_sub, sub_eq_zero] at hb; rw [hab, ha, hb]
  commutes' r := by
    have := hker _ (show π (Function.surjInv hπ (algebraMap R B r) - algebraMap R A r) = 0 by
      simp [Function.surjInv_eq, AlgHom.commutes])
    rwa [map_sub, AlgHom.commutes, sub_eq_zero] at this

end
end BeilinsonBernstein
