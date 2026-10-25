/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.TorusPeriodicLift
import Def.StatisticalMechanics.Code.Onsager.TorusIntersection.Part7


namespace StatMech.Onsager

open BigOperators StatMech.Ising

theorem ons_zeroFluxPotential_vertical_boundary
    (L : ℕ) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ evenSubgraphs (onsTorusGraph L))
    (p : ZMod L × ZMod L) :
    ons_zeroFluxPotential F p +
      ons_zeroFluxPotential F (p.1 - 1, p.2) =
        ons_zeroFluxVertical F p := by
  have hv := ons_zmodPrefix_add_pred_of_sum_zero
    (fun x ↦ ons_zeroFluxVertical F (x, p.2))
    (ons_zeroFluxVertical_sum_zero L F hF p.2) p.1
  unfold ons_zeroFluxPotential
  calc
    (ons_zmodPrefix
          (fun y ↦ ons_zeroFluxHorizontal F (0, y)) p.2 +
        ons_zmodPrefix
          (fun x ↦ ons_zeroFluxVertical F (x, p.2)) p.1) +
      (ons_zmodPrefix
          (fun y ↦ ons_zeroFluxHorizontal F (0, y)) p.2 +
        ons_zmodPrefix
          (fun x ↦ ons_zeroFluxVertical F (x, p.2)) (p.1 - 1)) =
        (ons_zmodPrefix
            (fun y ↦ ons_zeroFluxHorizontal F (0, y)) p.2 +
          ons_zmodPrefix
            (fun y ↦ ons_zeroFluxHorizontal F (0, y)) p.2) +
        (ons_zmodPrefix
            (fun x ↦ ons_zeroFluxVertical F (x, p.2)) p.1 +
          ons_zmodPrefix
            (fun x ↦ ons_zeroFluxVertical F (x, p.2)) (p.1 - 1)) := by
          abel
    _ = ons_zeroFluxVertical F p := by
      rw [CharTwo.add_self_eq_zero, zero_add, hv]

theorem ons_zeroFluxPotential_horizontal_boundary
    (L : ℕ) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ evenSubgraphs (onsTorusGraph L))
    (p : ZMod L × ZMod L) :
    ons_zeroFluxPotential F p +
      ons_zeroFluxPotential F (p.1, p.2 - 1) =
        ons_zeroFluxHorizontal F p := by
  have hnat : ∀ n : ℕ, n < L →
      ons_zeroFluxPotential F ((n : ZMod L), p.2) +
        ons_zeroFluxPotential F ((n : ZMod L), p.2 - 1) =
          ons_zeroFluxHorizontal F ((n : ZMod L), p.2) := by
    intro n hn
    induction n with
    | zero =>
        have hh := ons_zmodPrefix_add_pred_of_sum_zero
          (fun y ↦ ons_zeroFluxHorizontal F (0, y))
          (ons_zeroFluxHorizontal_sum_zero L F hF 0) p.2
        simpa only [Nat.cast_zero, ons_zeroFluxPotential,
          ons_zmodPrefix_zero, add_zero] using hh
    | succ n ih =>
        have hn : n < L := by omega
        have hnneg : (n : ZMod L) ≠ -1 := by
          intro heq
          have hval := congrArg ZMod.val heq
          rw [ZMod.val_natCast_of_lt hn, ons_zmod_val_neg_one] at hval
          omega
        have hcast : ((n + 1 : ℕ) : ZMod L) = (n : ZMod L) + 1 := by
          rw [Nat.cast_add, Nat.cast_one]
        have hv := ons_zmodPrefix_add_one
          (fun x ↦ ons_zeroFluxVertical F (x, p.2))
          (n : ZMod L) hnneg
        have hvpred := ons_zmodPrefix_add_one
          (fun x ↦ ons_zeroFluxVertical F (x, p.2 - 1))
          (n : ZMod L) hnneg
        have hsub : (((n + 1 : ℕ) : ZMod L) - 1) =
            (n : ZMod L) := by
          rw [hcast]
          ring
        have hdiv := ons_zeroFlux_divergence_zero L F hF
          (((n + 1 : ℕ) : ZMod L), p.2)
        rw [hsub] at hdiv
        have hstep :
            ons_zeroFluxHorizontal F ((n : ZMod L), p.2) +
              ons_zeroFluxVertical F (((n + 1 : ℕ) : ZMod L), p.2) +
              ons_zeroFluxVertical F
                (((n + 1 : ℕ) : ZMod L), p.2 - 1) =
              ons_zeroFluxHorizontal F
                (((n + 1 : ℕ) : ZMod L), p.2) := by
          have hzero :
              (ons_zeroFluxHorizontal F ((n : ZMod L), p.2) +
                ons_zeroFluxVertical F
                  (((n + 1 : ℕ) : ZMod L), p.2) +
                ons_zeroFluxVertical F
                  (((n + 1 : ℕ) : ZMod L), p.2 - 1)) +
                ons_zeroFluxHorizontal F
                  (((n + 1 : ℕ) : ZMod L), p.2) = 0 := by
            linear_combination hdiv
          exact (eq_neg_of_add_eq_zero_left hzero).trans
            (CharTwo.neg_eq _)
        rw [hcast]
        unfold ons_zeroFluxPotential
        rw [hv, hvpred]
        calc
          (ons_zmodPrefix
                (fun y ↦ ons_zeroFluxHorizontal F (0, y)) p.2 +
              (ons_zmodPrefix
                  (fun x ↦ ons_zeroFluxVertical F (x, p.2))
                    (n : ZMod L) +
                ons_zeroFluxVertical F
                  ((n : ZMod L) + 1, p.2))) +
            (ons_zmodPrefix
                (fun y ↦ ons_zeroFluxHorizontal F (0, y))
                  (p.2 - 1) +
              (ons_zmodPrefix
                  (fun x ↦ ons_zeroFluxVertical F (x, p.2 - 1))
                    (n : ZMod L) +
                ons_zeroFluxVertical F
                  ((n : ZMod L) + 1, p.2 - 1))) =
              (ons_zeroFluxPotential F ((n : ZMod L), p.2) +
                ons_zeroFluxPotential F ((n : ZMod L), p.2 - 1)) +
              ons_zeroFluxVertical F ((n : ZMod L) + 1, p.2) +
              ons_zeroFluxVertical F
                ((n : ZMod L) + 1, p.2 - 1) := by
                  unfold ons_zeroFluxPotential
                  abel
          _ = ons_zeroFluxHorizontal F
                ((n : ZMod L) + 1, p.2) := by
            rw [ih hn]
            rw [hcast] at hstep
            exact hstep
  simpa only [ZMod.natCast_zmod_val] using hnat p.1.val p.1.val_lt

theorem ons_zeroFlux_intersection_eq_zero
    (L : ℕ) [Fact (2 < L)]
    (F G : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ evenSubgraphs (onsTorusGraph L))
    (hG : G ∈ evenSubgraphs (onsTorusGraph L)) :
    (∑ p : ZMod L × ZMod L,
      (ons_zeroFluxHorizontal F p *
          ons_verticalZBit G (p.1, p.2 - 1) +
        ons_zeroFluxVertical F p *
          ons_horizontalZBit G (p.1 - 1, p.2))) = 0 := by
  have hvshift :
      (∑ p : ZMod L × ZMod L,
        ons_zeroFluxPotential F (p.1, p.2 - 1) *
          ons_verticalZBit G (p.1, p.2 - 1)) =
        ∑ p : ZMod L × ZMod L,
          ons_zeroFluxPotential F p * ons_verticalZBit G p := by
    simpa [sub_eq_add_neg] using
      (Equiv.sum_comp
        (Equiv.prodCongr (Equiv.refl (ZMod L))
          (Equiv.addRight (-1 : ZMod L)))
        (fun p : ZMod L × ZMod L ↦
          ons_zeroFluxPotential F p * ons_verticalZBit G p))
  have hhshift :
      (∑ p : ZMod L × ZMod L,
        ons_zeroFluxPotential F (p.1 - 1, p.2) *
          ons_horizontalZBit G (p.1 - 1, p.2)) =
        ∑ p : ZMod L × ZMod L,
          ons_zeroFluxPotential F p * ons_horizontalZBit G p := by
    simpa [sub_eq_add_neg] using
      (Equiv.sum_comp
        (Equiv.prodCongr (Equiv.addRight (-1 : ZMod L))
          (Equiv.refl (ZMod L)))
        (fun p : ZMod L × ZMod L ↦
          ons_zeroFluxPotential F p * ons_horizontalZBit G p))
  simp_rw [← ons_zeroFluxPotential_horizontal_boundary L F hF,
    ← ons_zeroFluxPotential_vertical_boundary L F hF, add_mul]
  calc
    (∑ p : ZMod L × ZMod L,
      (ons_zeroFluxPotential F p *
          ons_verticalZBit G (p.1, p.2 - 1) +
        ons_zeroFluxPotential F (p.1, p.2 - 1) *
          ons_verticalZBit G (p.1, p.2 - 1) +
        (ons_zeroFluxPotential F p *
            ons_horizontalZBit G (p.1 - 1, p.2) +
          ons_zeroFluxPotential F (p.1 - 1, p.2) *
            ons_horizontalZBit G (p.1 - 1, p.2)))) =
        (∑ p : ZMod L × ZMod L,
          ons_zeroFluxPotential F p *
            ons_verticalZBit G (p.1, p.2 - 1)) +
        (∑ p : ZMod L × ZMod L,
          ons_zeroFluxPotential F (p.1, p.2 - 1) *
            ons_verticalZBit G (p.1, p.2 - 1)) +
        (∑ p : ZMod L × ZMod L,
          ons_zeroFluxPotential F p *
            ons_horizontalZBit G (p.1 - 1, p.2)) +
        (∑ p : ZMod L × ZMod L,
          ons_zeroFluxPotential F (p.1 - 1, p.2) *
            ons_horizontalZBit G (p.1 - 1, p.2)) := by
          simp only [Finset.sum_add_distrib]
          abel
    _ =
        (∑ p : ZMod L × ZMod L,
          ons_zeroFluxPotential F p *
            ons_verticalZBit G (p.1, p.2 - 1)) +
        (∑ p : ZMod L × ZMod L,
          ons_zeroFluxPotential F p * ons_verticalZBit G p) +
        (∑ p : ZMod L × ZMod L,
          ons_zeroFluxPotential F p *
            ons_horizontalZBit G (p.1 - 1, p.2)) +
        (∑ p : ZMod L × ZMod L,
          ons_zeroFluxPotential F p * ons_horizontalZBit G p) := by
          rw [hvshift, hhshift]
    _ = ∑ p : ZMod L × ZMod L,
        ons_zeroFluxPotential F p *
          (ons_horizontalZBit G p +
            ons_horizontalZBit G (p.1 - 1, p.2) +
            ons_verticalZBit G p +
            ons_verticalZBit G (p.1, p.2 - 1)) := by
          simp only [mul_add, Finset.sum_add_distrib]
          abel
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro p _
      rw [ons_edgeZBits_divergence_zero L G hG p, mul_zero]

end StatMech.Onsager
