/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.TorusIntersection.Part8
import Def.StatisticalMechanics.Code.Onsager.TorusPrimitiveWinding


namespace StatMech.Onsager

open BigOperators

open StatMech.Onsager.BaseCase

theorem ons_sum_signedHorizontalBoundary_eq_zero
    {L : ℕ} [NeZero L]
    (P : (ZMod L × ZMod L) → ZMod 2) :
    ∑ p, ons_signedHorizontalBoundary P p = 0 := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro x hx
  unfold ons_signedHorizontalBoundary
  rw [Finset.sum_sub_distrib]
  have hshift :
      (∑ y : ZMod L, (P (x, y - 1)).val : ℤ) =
        ∑ y : ZMod L, ((P (x, y)).val : ℤ) := by
    simpa [sub_eq_add_neg] using
      (Equiv.sum_comp (Equiv.addRight (-1 : ZMod L))
        (fun y : ZMod L ↦ ((P (x, y)).val : ℤ)))
  rw [hshift, sub_self]

theorem ons_sum_signedVerticalBoundary_eq_zero
    {L : ℕ} [NeZero L]
    (P : (ZMod L × ZMod L) → ZMod 2) :
    ∑ p, ons_signedVerticalBoundary P p = 0 := by
  rw [Fintype.sum_prod_type]
  simp_rw [ons_signedVerticalBoundary]
  simp_rw [Finset.sum_sub_distrib]
  have hshift :
      (∑ x : ZMod L, ∑ y : ZMod L,
          ((P (x - 1, y)).val : ℤ)) =
        ∑ x : ZMod L, ∑ y : ZMod L,
          ((P (x, y)).val : ℤ) := by
    simpa [sub_eq_add_neg] using
      (Equiv.sum_comp (Equiv.addRight (-1 : ZMod L))
        (fun x : ZMod L ↦
          ∑ y : ZMod L, ((P (x, y)).val : ℤ)))
  rw [hshift, sub_self]

theorem ons_outgoingBoundaryCoeff_divergence
    {L : ℕ} (P : (ZMod L × ZMod L) → ZMod 2)
    (p : ZMod L × ZMod L) :
    ∑ mu : Fin 4, ons_outgoingBoundaryCoeff P p mu = 0 := by
  rw [Fin.sum_univ_four]
  simp only [ons_outgoingBoundaryCoeff]
  unfold ons_signedHorizontalBoundary ons_signedVerticalBoundary
  ring

theorem ons_intVal_sub_eq_zero_of_fin2_add_eq_zero
    (a b : ZMod 2) (h : a + b = 0) :
    (a.val : ℤ) - b.val = 0 := by
  have hab : a = b :=
    (eq_neg_of_add_eq_zero_left h).trans (CharTwo.neg_eq b)
  rw [hab, sub_self]

theorem ons_outgoingBoundaryCoeff_eq_zero_of_not_mem
    (L : ℕ) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ StatMech.Ising.evenSubgraphs (onsTorusGraph L))
    (hhom : ons_evenHomology L F = 0)
    (p : ZMod L × ZMod L) (mu : Fin 4)
    (hnot : ons_portEdge L (p, mu) ∉ F) :
    ons_outgoingBoundaryCoeff (ons_zeroFluxPotential F) p mu = 0 := by
  fin_cases mu
  · change ons_portEdge L (p, 0) ∉ F at hnot
    have hb :=
      ons_zeroFluxPotential_horizontal_boundary_of_zeroHomology
        L F hF hhom p
    have hz : ons_zeroFluxPotential F p +
        ons_zeroFluxPotential F (p.1, p.2 - 1) = 0 := by
      rw [hb]
      simp [ons_horizontalZBit, ons_horizontalBit, ons_edgeBit, hnot]
      rfl
    exact ons_intVal_sub_eq_zero_of_fin2_add_eq_zero _ _ hz
  · change ons_portEdge L (p, 1) ∉ F at hnot
    have hb :=
      ons_zeroFluxPotential_vertical_boundary_of_zeroHomology
        L F hF hhom p
    have hz : ons_zeroFluxPotential F (p.1 - 1, p.2) +
        ons_zeroFluxPotential F p = 0 := by
      rw [add_comm, hb]
      simp [ons_verticalZBit, ons_verticalBit, ons_edgeBit, hnot]
      rfl
    exact ons_intVal_sub_eq_zero_of_fin2_add_eq_zero _ _ hz
  · change ons_portEdge L (p, 2) ∉ F at hnot
    rw [ons_portEdge_west_eq_horizontal L p] at hnot
    have hb :=
      ons_zeroFluxPotential_horizontal_boundary_of_zeroHomology
        L F hF hhom (p.1 - 1, p.2)
    have hz : ons_zeroFluxPotential F (p.1 - 1, p.2) +
        ons_zeroFluxPotential F (p.1 - 1, p.2 - 1) = 0 := by
      rw [hb]
      simp [ons_horizontalZBit, ons_horizontalBit, ons_edgeBit, hnot]
      rfl
    change -(((ons_zeroFluxPotential F (p.1 - 1, p.2)).val : ℤ) -
      ((ons_zeroFluxPotential F (p.1 - 1, p.2 - 1)).val : ℤ)) = 0
    rw [ons_intVal_sub_eq_zero_of_fin2_add_eq_zero _ _ hz, neg_zero]
  · change ons_portEdge L (p, 3) ∉ F at hnot
    rw [ons_portEdge_south_eq_vertical L p] at hnot
    have hb :=
      ons_zeroFluxPotential_vertical_boundary_of_zeroHomology
        L F hF hhom (p.1, p.2 - 1)
    have hz : ons_zeroFluxPotential F (p.1 - 1, p.2 - 1) +
        ons_zeroFluxPotential F (p.1, p.2 - 1) = 0 := by
      rw [add_comm, hb]
      simp [ons_verticalZBit, ons_verticalBit, ons_edgeBit, hnot]
      rfl
    change -(((ons_zeroFluxPotential F (p.1 - 1, p.2 - 1)).val : ℤ) -
      ((ons_zeroFluxPotential F (p.1, p.2 - 1)).val : ℤ)) = 0
    rw [ons_intVal_sub_eq_zero_of_fin2_add_eq_zero _ _ hz, neg_zero]

theorem ons_outgoingBoundaryCoeff_dartRev
    {L : ℕ} (P : (ZMod L × ZMod L) → ZMod 2)
    (d : ons_Dart L) :
    ons_outgoingBoundaryCoeff P (ons_dartRev L d).1
        (ons_dartRev L d).2 =
      -ons_outgoingBoundaryCoeff P d.1 d.2 := by
  rcases d with ⟨p, mu⟩
  fin_cases mu <;>
    simp [ons_outgoingBoundaryCoeff, ons_signedHorizontalBoundary,
      ons_signedVerticalBoundary, ons_dartRev, ons_dirStep] <;>
    ring

theorem ons_fin4_sum_eq_two
    (f : Fin 4 → ℤ) (a b : Fin 4) (hab : a ≠ b)
    (hzero : ∀ mu, mu ≠ a → mu ≠ b → f mu = 0) :
    ∑ mu, f mu = f a + f b := by
  classical
  calc
    (∑ mu, f mu) = ∑ mu ∈ ({a, b} : Finset (Fin 4)), f mu := by
      symm
      apply Finset.sum_subset
      · simp
      · intro mu hmu hnot
        rw [Finset.mem_insert, Finset.mem_singleton] at hnot
        push_neg at hnot
        exact hzero mu hnot.1 hnot.2
    _ = f a + f b := by simp [hab]

end StatMech.Onsager
