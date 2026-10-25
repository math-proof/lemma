/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusPhysical.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalC1.Part6
import Theorem.StatisticalMechanics.Code.Ising.PressureBCIndep
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSignedPhysical.Part3
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager


theorem prod_neg_one_indicator
    {alpha : Type*} [DecidableEq alpha]
    (F : Finset alpha) (P : alpha → Prop) [DecidablePred P] :
    (∏ x ∈ F, if P x then (-1 : Real) else 1) =
      (-1 : Real) ^ (F.filter P).card := by
  induction F using Finset.induction_on with
  | empty => simp
  | @insert x F hx ih =>
      by_cases hP : P x
      · simp only [Finset.prod_insert hx, Finset.filter_insert, hP,
          if_true, ih]
        rw [Finset.card_insert_of_notMem (by simp [hx]), pow_succ]
        ring
      · simp [Finset.prod_insert hx, Finset.filter_insert, hP, hx, ih]

theorem triangularTorusSeamTwistSign_eq_mul
    (L : Nat) (chi : Fin 2 × Fin 2)
    (edge : Sym2 (ZMod L × ZMod L)) :
    triangularTorusSeamTwistSign L chi edge =
      (if triangularTorusXSeamEdge L edge then
          (-1 : Real) ^ chi.1.val else 1) *
        (if triangularTorusYSeamEdge L edge then
          (-1 : Real) ^ chi.2.val else 1) := by
  rcases chi with ⟨chi1, chi2⟩
  fin_cases chi1 <;> fin_cases chi2 <;>
    simp [triangularTorusSeamTwistSign, triangularTorusLinearCharacter] <;>
    split_ifs <;> norm_num


theorem prod_triangularTorusSeamTwistSign
    (L : Nat) (chi : Fin 2 × Fin 2)
    (F : Finset (Sym2 (ZMod L × ZMod L))) :
    (∏ edge ∈ F, triangularTorusSeamTwistSign L chi edge) =
      triangularTorusLinearCharacter chi (triangularTorusEvenHomology L F) := by
  classical
  rcases chi with ⟨chi1, chi2⟩
  simp_rw [triangularTorusSeamTwistSign_eq_mul]
  rw [Finset.prod_mul_distrib]
  fin_cases chi1 <;> fin_cases chi2
  · simp [triangularTorusLinearCharacter]
  · simp only [Fin.isValue, pow_zero, ite_self, Finset.prod_const_one,
      one_mul, pow_one]
    rw [prod_neg_one_indicator]
    simp [triangularTorusLinearCharacter, triangularTorusEvenHomology,
      neg_one_pow_eq_pow_mod_two]
  · simp only [Fin.isValue, pow_zero, ite_self, Finset.prod_const_one,
      pow_one, mul_one]
    rw [prod_neg_one_indicator]
    simp [triangularTorusLinearCharacter, triangularTorusEvenHomology,
      neg_one_pow_eq_pow_mod_two]
  · simp only [Fin.isValue, pow_one]
    rw [prod_neg_one_indicator, prod_neg_one_indicator, ← pow_add,
      neg_one_pow_eq_pow_mod_two]
    simp [triangularTorusLinearCharacter, triangularTorusEvenHomology,
      Nat.add_mod]
    conv_rhs => rw [neg_one_pow_eq_pow_mod_two]
    congr 1
    omega


theorem triangularTorusXSeamEdge_card
    (L : Nat) [Fact (2 < L)] :
    ((triangularTorusGraph L).edgeFinset.filter
      (triangularTorusXSeamEdge L)).card = 2 * L := by
  have h := sum_triangularPositiveEdgeSources (A := Nat) L
    (triangularTorusGraph L).edgeFinset (fun _ hedge => hedge)
    (fun edge => if triangularTorusXSeamEdge L edge then 1 else 0)
  simp_rw [triangularPositiveEdgeSources_edgeFinset,
    triangularTorusXSeamEdge_positiveEdge_iff] at h
  have hfirst :
      (Finset.univ.filter
        (fun p : ZMod L × ZMod L => p.1 = -1)).card = L := by
    have heq : Finset.univ.filter
        (fun p : ZMod L × ZMod L => p.1 = -1) =
        ({-1} : Finset (ZMod L)).product Finset.univ := by
      ext p
      rcases p with ⟨x, y⟩
      simp [eq_comm]
    rw [heq]
    simp [ZMod.card]
  have hc :
      ((triangularTorusGraph L).edgeFinset.filter
        (triangularTorusXSeamEdge L)).card = L + L := by
    simpa [Finset.sum_boole, Fin.sum_univ_three, hfirst] using h
  omega


theorem triangularTorusYSeamEdge_card
    (L : Nat) [Fact (2 < L)] :
    ((triangularTorusGraph L).edgeFinset.filter
      (triangularTorusYSeamEdge L)).card = 2 * L := by
  have h := sum_triangularPositiveEdgeSources (A := Nat) L
    (triangularTorusGraph L).edgeFinset (fun _ hedge => hedge)
    (fun edge => if triangularTorusYSeamEdge L edge then 1 else 0)
  simp_rw [triangularPositiveEdgeSources_edgeFinset,
    triangularTorusYSeamEdge_positiveEdge_iff] at h
  have hsecond :
      (Finset.univ.filter
        (fun p : ZMod L × ZMod L => p.2 = -1)).card = L := by
    have heq : Finset.univ.filter
        (fun p : ZMod L × ZMod L => p.2 = -1) =
        Finset.univ.product ({-1} : Finset (ZMod L)) := by
      ext p
      rcases p with ⟨x, y⟩
      simp [eq_comm]
    rw [heq]
    simp [ZMod.card]
  have hc :
      ((triangularTorusGraph L).edgeFinset.filter
        (triangularTorusYSeamEdge L)).card = L + L := by
    simpa [Finset.sum_boole, Fin.sum_univ_three, hsecond] using h
  omega


end StatMech.FrontierA
