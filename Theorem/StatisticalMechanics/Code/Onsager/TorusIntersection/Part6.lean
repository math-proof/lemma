/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.TorusPeriodicLift
import Def.StatisticalMechanics.Code.Onsager.TorusIntersection.Part6


namespace StatMech.Onsager

open BigOperators StatMech.Ising

theorem ons_zeroFlux_divergence_zero
    (L : ℕ) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ evenSubgraphs (onsTorusGraph L))
    (p : ZMod L × ZMod L) :
    ons_zeroFluxHorizontal F p +
      ons_zeroFluxHorizontal F (p.1 - 1, p.2) +
    ons_zeroFluxVertical F p +
      ons_zeroFluxVertical F (p.1, p.2 - 1) = 0 := by
  have hdiv := ons_edgeZBits_divergence_zero L F hF p
  have hx :
      (if p.2 = 0 then ons_xFlux F (-1) else 0) +
        (if p.2 = 0 then ons_xFlux F (-1) else 0) = 0 :=
    CharTwo.add_self_eq_zero _
  have hy :
      (if p.1 = 0 then ons_yFlux F (-1) else 0) +
        (if p.1 = 0 then ons_yFlux F (-1) else 0) = 0 :=
    CharTwo.add_self_eq_zero _
  unfold ons_zeroFluxHorizontal ons_zeroFluxVertical
  linear_combination hdiv + hx + hy

theorem ons_zeroFluxHorizontal_sum_zero
    (L : ℕ) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ evenSubgraphs (onsTorusGraph L))
    (x : ZMod L) :
    ∑ y : ZMod L, ons_zeroFluxHorizontal F (x, y) = 0 := by
  unfold ons_zeroFluxHorizontal
  rw [Finset.sum_add_distrib]
  change ons_xFlux F x +
    (∑ y : ZMod L, if y = 0 then ons_xFlux F (-1) else 0) = 0
  rw [ons_xFlux_eq_neg_one L F hF x]
  simp
  exact CharTwo.add_self_eq_zero _

theorem ons_zeroFluxVertical_sum_zero
    (L : ℕ) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ evenSubgraphs (onsTorusGraph L))
    (y : ZMod L) :
    ∑ x : ZMod L, ons_zeroFluxVertical F (x, y) = 0 := by
  unfold ons_zeroFluxVertical
  rw [Finset.sum_add_distrib]
  change ons_yFlux F y +
    (∑ x : ZMod L, if x = 0 then ons_yFlux F (-1) else 0) = 0
  rw [ons_yFlux_eq_neg_one L F hF y]
  simp
  exact CharTwo.add_self_eq_zero _

end StatMech.Onsager
