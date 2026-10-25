/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalCoefficient.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationCycleExponent.Part2
import Def.StatisticalMechanics.Code.Onsager.DecorationFormalCoefficient.Part2


namespace StatMech.Onsager

open BigOperators Finset SimpleGraph StatMech.Ising

theorem ons_eq_finsetExponent_support_of_squarefree
    {E : Type*} [DecidableEq E] (m : E →₀ ℕ)
    (hm : ons_IsSquarefreeExponent m) :
    m = ons_finsetExponent m.support := by
  ext edge
  rw [ons_finsetExponent_apply]
  by_cases hedge : edge ∈ m.support
  · rw [if_pos hedge]
    have hpos : 0 < m edge :=
      Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hedge)
    have hle := hm edge
    omega
  · rw [if_neg hedge]
    exact Finsupp.notMem_support_iff.mp hedge

theorem ons_decoratedSpinPolynomial_coeff_eq_zero_of_not_squarefree
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    (m : ons_DecEdge L →₀ ℕ)
    (hm : ¬ ons_IsSquarefreeExponent m) :
    MvPowerSeries.coeff m
        (ons_decoratedSpinPolynomial L a b :
          MvPowerSeries (ons_DecEdge L) ℂ) = 0 := by
  classical
  rw [MvPolynomial.coeff_coe]
  unfold ons_decoratedSpinPolynomial
  rw [MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro D hD
  rw [MvPolynomial.coeff_monomial, if_neg]
  intro heq
  apply hm
  intro edge
  rw [← heq, ons_finsetExponent_apply]
  split <;> omega

theorem ons_decoratedFormalKacWardIdentity_of_nonsquarefree_zero
    (L : ℕ) [Fact (2 < L)]
    (hnonsquare : ∀ (a b : Fin 2) (m : ons_DecEdge L →₀ ℕ),
      ¬ ons_IsSquarefreeExponent m →
      MvPowerSeries.coeff m
        (ons_decFormalRoot L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b)) = 0) :
    ons_decoratedFormalKacWardIdentity L := by
  intro a b
  ext m
  by_cases hm : ons_IsSquarefreeExponent m
  · rw [ons_eq_finsetExponent_support_of_squarefree m hm]
    exact ons_decFormalRoot_coeff_finsetExponent L a b m.support
  · rw [hnonsquare a b m hm,
      ons_decoratedSpinPolynomial_coeff_eq_zero_of_not_squarefree
        L a b m hm]

end StatMech.Onsager
