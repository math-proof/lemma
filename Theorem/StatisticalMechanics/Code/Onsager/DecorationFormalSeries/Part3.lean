/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSeries.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationTransitionWeights.Part2
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Substitution
import Def.StatisticalMechanics.Code.Onsager.DecorationFormalSeries.Part3


namespace StatMech.Onsager

open BigOperators Finset

theorem ons_finsetExponent_insert
    {E : Type*} [DecidableEq E] (S : Finset E) (edge : E)
    (hedge : edge ∉ S) :
    ons_finsetExponent (insert edge S) =
      Finsupp.single edge 1 + ons_finsetExponent S := by
  classical
  simp [ons_finsetExponent, Finset.sum_insert hedge]

theorem ons_finsetExponent_image
    {E F : Type*} [DecidableEq E] [DecidableEq F]
    (S : Finset E) (f : E → F) (hf : Set.InjOn f S) :
    ons_finsetExponent (S.image f) =
      ∑ edge ∈ S, Finsupp.single (f edge) 1 := by
  classical
  unfold ons_finsetExponent
  rw [Finset.sum_image]
  exact hf

@[simp] theorem ons_finsetExponent_apply
    {E : Type*} [DecidableEq E] (S : Finset E) (edge : E) :
    ons_finsetExponent S edge = if edge ∈ S then 1 else 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [ons_finsetExponent]
  | @insert e S he ih =>
      have hexp : ons_finsetExponent (insert e S) =
          Finsupp.single e 1 + ons_finsetExponent S := by
        exact ons_finsetExponent_insert S e he
      rw [hexp, Finsupp.add_apply, ih]
      by_cases hedge : edge = e
      · subst edge
        simp [he]
      · simp [hedge]

theorem ons_finsetExponent_injective
    {E : Type*} [DecidableEq E] :
    Function.Injective (ons_finsetExponent : Finset E → E →₀ ℕ) := by
  intro S T h
  ext edge
  constructor
  · intro hS
    have happ := DFunLike.congr_fun h edge
    rw [ons_finsetExponent_apply, ons_finsetExponent_apply,
      if_pos hS] at happ
    by_contra hT
    rw [if_neg hT] at happ
    omega
  · intro hT
    have happ := DFunLike.congr_fun h edge
    rw [ons_finsetExponent_apply, ons_finsetExponent_apply,
      if_pos hT] at happ
    by_contra hS
    rw [if_neg hS] at happ
    omega

theorem ons_finsetExponent_prod
    {E R : Type*} [DecidableEq E] [CommMonoid R]
    (S : Finset E) (weight : E → R) :
    (ons_finsetExponent S).prod (fun edge n ↦ weight edge ^ n) =
      ∏ edge ∈ S, weight edge := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [ons_finsetExponent]
  | @insert edge S hedge ih =>
      have hexp : ons_finsetExponent (insert edge S) =
          Finsupp.single edge 1 + ons_finsetExponent S := by
        exact ons_finsetExponent_insert S edge hedge
      rw [hexp, Finsupp.prod_add_index]
      · rw [Finsupp.prod_single_index]
        · simp [ih, hedge]
        · simp
      · intro e he
        simp
      · intro e he n₁ n₂
        simp [pow_add]

end StatMech.Onsager
