/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.TorusIntersection.Part8
import Def.StatisticalMechanics.Code.FrontierD.IntegralSquareTorusIntersection.Part4
open scoped BigOperators
open Finset


namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section

namespace IntegralSquareTorusCycle

variable {L : Nat} [Fact (2 < L)]


theorem zeroFlux_intersection_eq_zero
    (C D : IntegralSquareTorusCycle L) :
    ∑ p : ZMod L × ZMod L,
      (C.zeroFluxHorizontal p * D.vertical (p.1, p.2 - 1) -
        C.zeroFluxVertical p * D.horizontal (p.1 - 1, p.2)) = 0 := by
  let P := C.streamPotential
  have hvshift :
      (∑ p : ZMod L × ZMod L,
        P (p.1, p.2 - 1) * D.vertical (p.1, p.2 - 1)) =
      ∑ p : ZMod L × ZMod L, P p * D.vertical p := by
    simpa [sub_eq_add_neg] using
      (Equiv.sum_comp
        (Equiv.prodCongr (Equiv.refl (ZMod L))
          (Equiv.addRight (-1 : ZMod L)))
        (fun p : ZMod L × ZMod L => P p * D.vertical p))
  have hhshift :
      (∑ p : ZMod L × ZMod L,
        P (p.1 - 1, p.2) * D.horizontal (p.1 - 1, p.2)) =
      ∑ p : ZMod L × ZMod L, P p * D.horizontal p := by
    simpa [sub_eq_add_neg] using
      (Equiv.sum_comp
        (Equiv.prodCongr (Equiv.addRight (-1 : ZMod L))
          (Equiv.refl (ZMod L)))
        (fun p : ZMod L × ZMod L => P p * D.horizontal p))
  simp_rw [← C.streamPotential_horizontal_boundary,
    ← C.streamPotential_vertical_boundary]
  change (∑ p : ZMod L × ZMod L,
    ((P p - P (p.1, p.2 - 1)) * D.vertical (p.1, p.2 - 1) -
      (P (p.1 - 1, p.2) - P p) * D.horizontal (p.1 - 1, p.2))) = 0
  simp only [sub_mul, Finset.sum_sub_distrib]
  rw [hvshift, hhshift]
  calc
    (∑ p, P p * D.vertical (p.1, p.2 - 1)) -
          (∑ p, P p * D.vertical p) -
        ((∑ p, P p * D.horizontal p) -
          ∑ p, P p * D.horizontal (p.1 - 1, p.2)) =
      ∑ p, P p *
        (D.vertical (p.1, p.2 - 1) - D.vertical p -
          D.horizontal p + D.horizontal (p.1 - 1, p.2)) := by
            simp only [mul_add, mul_sub, Finset.sum_add_distrib,
              Finset.sum_sub_distrib]
            ring
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro p _
      have hdiv := D.divergence_zero p
      rw [show D.vertical (p.1, p.2 - 1) - D.vertical p -
          D.horizontal p + D.horizontal (p.1 - 1, p.2) = 0 by
        linarith]
      ring

theorem intersection_eq_flux_det (C D : IntegralSquareTorusCycle L) :
    C.intersection D =
      C.xFlux (-1) * D.yFlux (-1) -
        C.yFlux (-1) * D.xFlux (-1) := by
  unfold intersection
  have hH : ∀ p, C.horizontal p = C.zeroFluxHorizontal p +
      if p.2 = 0 then C.xFlux (-1) else 0 := by
    intro p
    unfold zeroFluxHorizontal
    ring
  have hV : ∀ p, C.vertical p = C.zeroFluxVertical p +
      if p.1 = 0 then C.yFlux (-1) else 0 := by
    intro p
    unfold zeroFluxVertical
    ring
  simp_rw [hH, hV]
  calc
    (∑ p : ZMod L × ZMod L,
      ((C.zeroFluxHorizontal p + if p.2 = 0 then C.xFlux (-1) else 0) *
          D.vertical (p.1, p.2 - 1) -
        (C.zeroFluxVertical p + if p.1 = 0 then C.yFlux (-1) else 0) *
          D.horizontal (p.1 - 1, p.2))) =
        (∑ p : ZMod L × ZMod L,
          (C.zeroFluxHorizontal p * D.vertical (p.1, p.2 - 1) -
          C.zeroFluxVertical p * D.horizontal (p.1 - 1, p.2))) +
        (∑ p : ZMod L × ZMod L,
          (if p.2 = 0 then C.xFlux (-1) else 0) *
          D.vertical (p.1, p.2 - 1)) -
        (∑ p : ZMod L × ZMod L,
          (if p.1 = 0 then C.yFlux (-1) else 0) *
          D.horizontal (p.1 - 1, p.2)) := by
            simp only [add_mul, Finset.sum_sub_distrib,
              Finset.sum_add_distrib]
            ring
    _ = C.xFlux (-1) * D.yFlux (-1) -
        C.yFlux (-1) * D.xFlux (-1) := by
      rw [C.zeroFlux_intersection_eq_zero D, zero_add]
      have hx :
          (∑ p : ZMod L × ZMod L,
            (if p.2 = 0 then C.xFlux (-1) else 0) *
              D.vertical (p.1, p.2 - 1)) =
            C.xFlux (-1) * D.yFlux (-1) := by
        rw [Fintype.sum_prod_type]
        simp
        unfold yFlux
        rw [Finset.mul_sum]
      have hy :
          (∑ p : ZMod L × ZMod L,
            (if p.1 = 0 then C.yFlux (-1) else 0) *
              D.horizontal (p.1 - 1, p.2)) =
            C.yFlux (-1) * D.xFlux (-1) := by
        rw [Fintype.sum_prod_type]
        simp
        unfold xFlux
        rw [Finset.mul_sum]
      rw [hx, hy]


end IntegralSquareTorusCycle
end
end StatMech.FrontierD
