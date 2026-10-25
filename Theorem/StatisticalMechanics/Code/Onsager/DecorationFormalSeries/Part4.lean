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
import Def.StatisticalMechanics.Code.Onsager.DecorationFormalSeries.Part4


namespace StatMech.Onsager

open BigOperators Finset

theorem ons_decoratedSpinPolynomial_eval
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    (decWeight : ons_DecEdge L → ℂ) :
    MvPolynomial.eval decWeight (ons_decoratedSpinPolynomial L a b) =
      ons_decoratedFullWeightedSpinSum L decWeight a b := by
  classical
  unfold ons_decoratedSpinPolynomial ons_decoratedFullWeightedSpinSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro D hD
  rw [MvPolynomial.eval_monomial, ons_finsetExponent_prod]

theorem ons_decoratedSpinPolynomial_coeff
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    (D : ons_DecoratedEvenSubgraph L) :
    MvPolynomial.coeff (ons_finsetExponent D.1)
        (ons_decoratedSpinPolynomial L a b) =
      (ons_spinCharacter a b
        (ons_evenHomology L (ons_originalEdgesOfDecorated L D)) : ℂ) := by
  classical
  unfold ons_decoratedSpinPolynomial
  rw [MvPolynomial.coeff_sum]
  rw [Fintype.sum_eq_single D]
  · rw [MvPolynomial.coeff_monomial]
    simp
  · intro D' hne
    rw [MvPolynomial.coeff_monomial]
    split_ifs with heq
    · have hval : D'.1 = D.1 :=
        ons_finsetExponent_injective heq
      exact (hne (Subtype.ext hval)).elim
    · rfl


end StatMech.Onsager
