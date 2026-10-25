/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.TorusIntersection.Part8
import Def.StatisticalMechanics.Code.Onsager.TorusPrimitiveWinding.Part2


namespace StatMech.Onsager

open BigOperators

open StatMech.Onsager.BaseCase

theorem ons_loopBoundaryCoeff_pred
    {L n : ℕ} [Fact (2 < L)] [NeZero n]
    (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
    (hsite : Function.Injective (fun k ↦ (v k).1))
    (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2)
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ StatMech.Ising.evenSubgraphs (onsTorusGraph L))
    (hFedge : F = ons_dartEdgeSet v)
    (hhom : ons_evenHomology L F = 0)
    (k : Fin n) :
    ons_loopBoundaryCoeff (ons_zeroFluxPotential F) v k =
      ons_loopBoundaryCoeff (ons_zeroFluxPotential F) v (k - 1) := by
  let P := ons_zeroFluxPotential F
  let a := ons_liftDir v k
  let b := ons_liftDir v (k - 1) + 2
  have hab : a ≠ b := by
    have h := ons_liftDir_nonUturn v hnu (k - 1)
    simpa [a, b] using h
  have hzero : ∀ mu, mu ≠ a → mu ≠ b →
      ons_outgoingBoundaryCoeff P (ons_liftSite v k) mu = 0 := by
    intro mu hma hmb
    apply ons_outgoingBoundaryCoeff_eq_zero_of_not_mem
      L F hF hhom
    rw [hFedge]
    intro hmem
    have hm := (ons_portEdge_mem_dartEdgeSet_at_liftSite_iff
      v hvalid hsite k mu).mp hmem
    exact hm.elim hma hmb
  have hdiv := ons_outgoingBoundaryCoeff_divergence
    P (ons_liftSite v k)
  rw [ons_fin4_sum_eq_two
    (fun mu ↦ ons_outgoingBoundaryCoeff P (ons_liftSite v k) mu)
    a b hab hzero] at hdiv
  have hincoming :
      ons_outgoingBoundaryCoeff P (ons_liftSite v k) b =
        -ons_loopBoundaryCoeff P v (k - 1) := by
    have hd := ons_liftSite_incomingRevDart v hvalid k
    have hr := ons_outgoingBoundaryCoeff_dartRev P (v (-k + 1))
    rw [← hd] at hr
    have hidx : -k + 1 = 1 - k := by abel
    rw [hidx] at hr
    simpa [b, ons_loopBoundaryCoeff, ons_liftSite, ons_liftDir] using hr
  change ons_outgoingBoundaryCoeff P (ons_liftSite v k) a = _
  rw [hincoming] at hdiv
  linear_combination hdiv

theorem ons_fin_pred_invariant
    {n : ℕ} [NeZero n] (f : Fin n → ℤ)
    (hpred : ∀ k, f k = f (k - 1)) :
    ∀ k, f k = f 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  intro k
  induction k using Fin.induction with
  | zero => rfl
  | succ i ih =>
      rw [hpred i.succ]
      have hsub : i.succ - 1 = i.castSucc := by
        have hsucc : i.succ = i.castSucc + 1 := by
          have hm : 0 < m := by
            by_contra h
            have hm0 : m = 0 := Nat.eq_zero_of_not_pos h
            subst m
            exact Fin.elim0 i
          have hone : (1 : Fin (m + 1)).val = 1 := by
            change 1 % (m + 1) = 1
            exact Nat.mod_eq_of_lt (by omega)
          apply Fin.ext
          simp only [Fin.val_succ, Fin.val_add, Fin.val_castSucc]
          rw [hone]
          rw [Nat.mod_eq_of_lt (by omega)]
        rw [hsucc]
        abel
      rw [hsub, ih]

theorem ons_intVal_sub_ne_zero_of_fin2_add_eq_one
    (a b : ZMod 2) (h : a + b = 1) :
    (a.val : ℤ) - b.val ≠ 0 := by
  intro hz
  have hval : a.val = b.val := by omega
  have hab : a = b := ZMod.val_injective 2 hval
  subst b
  have hzero : a + a = 0 := CharTwo.add_self_eq_zero a
  rw [hzero] at h
  exact zero_ne_one h

theorem ons_outgoingBoundaryCoeff_ne_zero_of_mem
    (L : ℕ) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ StatMech.Ising.evenSubgraphs (onsTorusGraph L))
    (hhom : ons_evenHomology L F = 0)
    (p : ZMod L × ZMod L) (mu : Fin 4)
    (hmem : ons_portEdge L (p, mu) ∈ F) :
    ons_outgoingBoundaryCoeff (ons_zeroFluxPotential F) p mu ≠ 0 := by
  fin_cases mu
  · change ons_portEdge L (p, 0) ∈ F at hmem
    have hb :=
      ons_zeroFluxPotential_horizontal_boundary_of_zeroHomology
        L F hF hhom p
    have hone : ons_zeroFluxPotential F p +
        ons_zeroFluxPotential F (p.1, p.2 - 1) = 1 := by
      rw [hb]
      simp [ons_horizontalZBit, ons_horizontalBit, ons_edgeBit, hmem]
      rfl
    exact ons_intVal_sub_ne_zero_of_fin2_add_eq_one _ _ hone
  · change ons_portEdge L (p, 1) ∈ F at hmem
    have hb :=
      ons_zeroFluxPotential_vertical_boundary_of_zeroHomology
        L F hF hhom p
    have hone : ons_zeroFluxPotential F (p.1 - 1, p.2) +
        ons_zeroFluxPotential F p = 1 := by
      rw [add_comm, hb]
      simp [ons_verticalZBit, ons_verticalBit, ons_edgeBit, hmem]
      rfl
    exact ons_intVal_sub_ne_zero_of_fin2_add_eq_one _ _ hone
  · change ons_portEdge L (p, 2) ∈ F at hmem
    rw [ons_portEdge_west_eq_horizontal L p] at hmem
    have hb :=
      ons_zeroFluxPotential_horizontal_boundary_of_zeroHomology
        L F hF hhom (p.1 - 1, p.2)
    have hone : ons_zeroFluxPotential F (p.1 - 1, p.2) +
        ons_zeroFluxPotential F (p.1 - 1, p.2 - 1) = 1 := by
      rw [hb]
      simp [ons_horizontalZBit, ons_horizontalBit, ons_edgeBit, hmem]
      rfl
    change -(((ons_zeroFluxPotential F (p.1 - 1, p.2)).val : ℤ) -
      ((ons_zeroFluxPotential F (p.1 - 1, p.2 - 1)).val : ℤ)) ≠ 0
    exact neg_ne_zero.mpr
      (ons_intVal_sub_ne_zero_of_fin2_add_eq_one _ _ hone)
  · change ons_portEdge L (p, 3) ∈ F at hmem
    rw [ons_portEdge_south_eq_vertical L p] at hmem
    have hb :=
      ons_zeroFluxPotential_vertical_boundary_of_zeroHomology
        L F hF hhom (p.1, p.2 - 1)
    have hone : ons_zeroFluxPotential F (p.1 - 1, p.2 - 1) +
        ons_zeroFluxPotential F (p.1, p.2 - 1) = 1 := by
      rw [add_comm, hb]
      simp [ons_verticalZBit, ons_verticalBit, ons_edgeBit, hmem]
      rfl
    change -(((ons_zeroFluxPotential F (p.1 - 1, p.2 - 1)).val : ℤ) -
      ((ons_zeroFluxPotential F (p.1, p.2 - 1)).val : ℤ)) ≠ 0
    exact neg_ne_zero.mpr
      (ons_intVal_sub_ne_zero_of_fin2_add_eq_one _ _ hone)

theorem ons_xWrapSign_eq_zero_of_not
    {L : ℕ} (d : ons_Dart L) (h : ¬ons_xWrap d) :
    ons_xWrapSign d = 0 := by
  rcases d with ⟨p, mu⟩
  fin_cases mu <;> simp [ons_xWrap, ons_xWrapSign] at h ⊢ <;>
    assumption

theorem ons_yWrapSign_eq_zero_of_not
    {L : ℕ} (d : ons_Dart L) (h : ¬ons_yWrap d) :
    ons_yWrapSign d = 0 := by
  rcases d with ⟨p, mu⟩
  fin_cases mu <;> simp [ons_yWrap, ons_yWrapSign] at h ⊢ <;>
    assumption

theorem ons_portEdge_eq_xSeamPortEdge_of_xWrap
    {L : ℕ} [Fact (2 < L)] (d : ons_Dart L)
    (h : ons_xWrap d) :
    ons_portEdge L d = ons_xSeamPortEdge L d.1.2 := by
  rcases d with ⟨⟨x, y⟩, mu⟩
  fin_cases mu <;> simp [ons_xWrap] at h
  · subst x
    rfl
  · subst x
    simpa [ons_xSeamPortEdge] using
      ons_portEdge_west_eq_horizontal L ((0 : ZMod L), y)

theorem ons_portEdge_eq_ySeamPortEdge_of_yWrap
    {L : ℕ} [Fact (2 < L)] (d : ons_Dart L)
    (h : ons_yWrap d) :
    ons_portEdge L d = ons_ySeamPortEdge L d.1.1 := by
  rcases d with ⟨⟨x, y⟩, mu⟩
  fin_cases mu <;> simp [ons_yWrap] at h
  · subst y
    rfl
  · subst y
    simpa [ons_ySeamPortEdge] using
      ons_portEdge_south_eq_vertical L (x, (0 : ZMod L))

theorem ons_boundaryCoeff_mul_xWrapSign
    {L : ℕ} [Fact (2 < L)]
    (P : (ZMod L × ZMod L) → ZMod 2)
    (d : ons_Dart L) (h : ons_xWrap d) :
    ons_outgoingBoundaryCoeff P d.1 d.2 * ons_xWrapSign d =
      ons_signedHorizontalBoundary P (-1, d.1.2) := by
  rcases d with ⟨⟨x, y⟩, mu⟩
  fin_cases mu <;> simp [ons_xWrap] at h
  · subst x
    simp [ons_xWrapSign, ons_outgoingBoundaryCoeff]
  · subst x
    simp [ons_xWrapSign, ons_outgoingBoundaryCoeff]

theorem ons_boundaryCoeff_mul_yWrapSign
    {L : ℕ} [Fact (2 < L)]
    (P : (ZMod L × ZMod L) → ZMod 2)
    (d : ons_Dart L) (h : ons_yWrap d) :
    ons_outgoingBoundaryCoeff P d.1 d.2 * ons_yWrapSign d =
      ons_signedVerticalBoundary P (d.1.1, -1) := by
  rcases d with ⟨⟨x, y⟩, mu⟩
  fin_cases mu <;> simp [ons_yWrap] at h
  · subst y
    simp [ons_yWrapSign, ons_outgoingBoundaryCoeff]
  · subst y
    simp [ons_yWrapSign, ons_outgoingBoundaryCoeff]

theorem ons_sum_signedHorizontalBoundary_fixed_eq_zero
    {L : ℕ} [NeZero L]
    (P : (ZMod L × ZMod L) → ZMod 2) (x : ZMod L) :
    ∑ y, ons_signedHorizontalBoundary P (x, y) = 0 := by
  unfold ons_signedHorizontalBoundary
  rw [Finset.sum_sub_distrib]
  have hshift :
      (∑ y : ZMod L, ((P (x, y - 1)).val : ℤ)) =
        ∑ y : ZMod L, ((P (x, y)).val : ℤ) := by
    simpa [sub_eq_add_neg] using
      (Equiv.sum_comp (Equiv.addRight (-1 : ZMod L))
        (fun y : ZMod L ↦ ((P (x, y)).val : ℤ)))
  rw [hshift, sub_self]

theorem ons_sum_signedVerticalBoundary_fixed_eq_zero
    {L : ℕ} [NeZero L]
    (P : (ZMod L × ZMod L) → ZMod 2) (y : ZMod L) :
    ∑ x, ons_signedVerticalBoundary P (x, y) = 0 := by
  unfold ons_signedVerticalBoundary
  rw [Finset.sum_sub_distrib]
  have hshift :
      (∑ x : ZMod L, ((P (x - 1, y)).val : ℤ)) =
        ∑ x : ZMod L, ((P (x, y)).val : ℤ) := by
    simpa [sub_eq_add_neg] using
      (Equiv.sum_comp (Equiv.addRight (-1 : ZMod L))
        (fun x : ZMod L ↦ ((P (x, y)).val : ℤ)))
  rw [hshift, sub_self]

theorem ons_sum_boundaryCoeff_mul_xWrapSign_eq_zero
    {L n : ℕ} [Fact (2 < L)] [NeZero n]
    (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
    (hsite : Function.Injective (fun k ↦ (v k).1))
    (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2)
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ StatMech.Ising.evenSubgraphs (onsTorusGraph L))
    (hFedge : F = ons_dartEdgeSet v)
    (hhom : ons_evenHomology L F = 0) :
    ∑ j, ons_outgoingBoundaryCoeff (ons_zeroFluxPotential F)
        (v j).1 (v j).2 * ons_xWrapSign (v j) = 0 := by
  classical
  let P := ons_zeroFluxPotential F
  let S := (Finset.univ : Finset (Fin n)).filter
    (fun j ↦ ons_xWrap (v j))
  let T := (Finset.univ : Finset (ZMod L)).filter
    (fun y ↦ ons_xSeamPortEdge L y ∈ F)
  let f : Fin n → ℤ := fun j ↦
    ons_outgoingBoundaryCoeff P (v j).1 (v j).2 *
      ons_xWrapSign (v j)
  calc
    (∑ j, ons_outgoingBoundaryCoeff P (v j).1 (v j).2 *
        ons_xWrapSign (v j)) = ∑ j ∈ S, f j := by
      symm
      apply Finset.sum_subset
      · simp [S]
      · intro j hj hnot
        have hnwrap : ¬ons_xWrap (v j) := by
          intro hw
          apply hnot
          simp [S, hw]
        change ons_outgoingBoundaryCoeff P (v j).1 (v j).2 *
          ons_xWrapSign (v j) = 0
        rw [ons_xWrapSign_eq_zero_of_not (v j) hnwrap, mul_zero]
    _ = ∑ y ∈ T, ons_signedHorizontalBoundary P (-1, y) := by
      apply Finset.sum_bij (fun j _ ↦ (v j).1.2)
      · intro j hj
        rw [Finset.mem_filter] at hj ⊢
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [hFedge, ons_dartEdgeSet, Finset.mem_image]
        exact ⟨j, Finset.mem_univ _,
          ons_portEdge_eq_xSeamPortEdge_of_xWrap (v j) hj.2⟩
      · intro a ha b hb hab
        apply ons_portEdge_loop_injective v hvalid hsite hnu
        change ons_portEdge L (v a) = ons_portEdge L (v b)
        rw [ons_portEdge_eq_xSeamPortEdge_of_xWrap
              (v a) (Finset.mem_filter.mp ha).2,
          ons_portEdge_eq_xSeamPortEdge_of_xWrap
              (v b) (Finset.mem_filter.mp hb).2,
          hab]
      · intro y hy
        have hyF := (Finset.mem_filter.mp hy).2
        rw [hFedge, ons_dartEdgeSet, Finset.mem_image] at hyF
        obtain ⟨j, hj, hedge⟩ := hyF
        have hwrap : ons_xWrap (v j) := by
          apply (ons_xSeamEdge_portEdge_iff (v j)).mp
          rw [hedge]
          exact ons_xSeamEdge_xSeamPortEdge L y
        have hcoord : (v j).1.2 = y := by
          apply ons_xSeamPortEdge_injective L
          rw [← ons_portEdge_eq_xSeamPortEdge_of_xWrap (v j) hwrap,
            hedge]
        exact ⟨j, Finset.mem_filter.mpr ⟨hj, hwrap⟩, hcoord⟩
      · intro j hj
        exact ons_boundaryCoeff_mul_xWrapSign P (v j)
          (Finset.mem_filter.mp hj).2
    _ = ∑ y : ZMod L, ons_signedHorizontalBoundary P (-1, y) := by
      apply Finset.sum_subset
      · simp [T]
      · intro y hy hnot
        have hnotF : ons_xSeamPortEdge L y ∉ F := by
          intro hmem
          apply hnot
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩
        have hz := ons_outgoingBoundaryCoeff_eq_zero_of_not_mem
          L F hF hhom ((-1 : ZMod L), y) 0 (by
            simpa [ons_xSeamPortEdge] using hnotF)
        simpa [ons_outgoingBoundaryCoeff] using hz
    _ = 0 := ons_sum_signedHorizontalBoundary_fixed_eq_zero P (-1)

theorem ons_sum_boundaryCoeff_mul_yWrapSign_eq_zero
    {L n : ℕ} [Fact (2 < L)] [NeZero n]
    (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
    (hsite : Function.Injective (fun k ↦ (v k).1))
    (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2)
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ StatMech.Ising.evenSubgraphs (onsTorusGraph L))
    (hFedge : F = ons_dartEdgeSet v)
    (hhom : ons_evenHomology L F = 0) :
    ∑ j, ons_outgoingBoundaryCoeff (ons_zeroFluxPotential F)
        (v j).1 (v j).2 * ons_yWrapSign (v j) = 0 := by
  classical
  let P := ons_zeroFluxPotential F
  let S := (Finset.univ : Finset (Fin n)).filter
    (fun j ↦ ons_yWrap (v j))
  let T := (Finset.univ : Finset (ZMod L)).filter
    (fun x ↦ ons_ySeamPortEdge L x ∈ F)
  let f : Fin n → ℤ := fun j ↦
    ons_outgoingBoundaryCoeff P (v j).1 (v j).2 *
      ons_yWrapSign (v j)
  calc
    (∑ j, ons_outgoingBoundaryCoeff P (v j).1 (v j).2 *
        ons_yWrapSign (v j)) = ∑ j ∈ S, f j := by
      symm
      apply Finset.sum_subset
      · simp [S]
      · intro j hj hnot
        have hnwrap : ¬ons_yWrap (v j) := by
          intro hw
          apply hnot
          simp [S, hw]
        change ons_outgoingBoundaryCoeff P (v j).1 (v j).2 *
          ons_yWrapSign (v j) = 0
        rw [ons_yWrapSign_eq_zero_of_not (v j) hnwrap, mul_zero]
    _ = ∑ x ∈ T, ons_signedVerticalBoundary P (x, -1) := by
      apply Finset.sum_bij (fun j _ ↦ (v j).1.1)
      · intro j hj
        rw [Finset.mem_filter] at hj ⊢
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [hFedge, ons_dartEdgeSet, Finset.mem_image]
        exact ⟨j, Finset.mem_univ _,
          ons_portEdge_eq_ySeamPortEdge_of_yWrap (v j) hj.2⟩
      · intro a ha b hb hab
        apply ons_portEdge_loop_injective v hvalid hsite hnu
        change ons_portEdge L (v a) = ons_portEdge L (v b)
        rw [ons_portEdge_eq_ySeamPortEdge_of_yWrap
              (v a) (Finset.mem_filter.mp ha).2,
          ons_portEdge_eq_ySeamPortEdge_of_yWrap
              (v b) (Finset.mem_filter.mp hb).2,
          hab]
      · intro x hx
        have hxF := (Finset.mem_filter.mp hx).2
        rw [hFedge, ons_dartEdgeSet, Finset.mem_image] at hxF
        obtain ⟨j, hj, hedge⟩ := hxF
        have hwrap : ons_yWrap (v j) := by
          apply (ons_ySeamEdge_portEdge_iff (v j)).mp
          rw [hedge]
          exact ons_ySeamEdge_ySeamPortEdge L x
        have hcoord : (v j).1.1 = x := by
          apply ons_ySeamPortEdge_injective L
          rw [← ons_portEdge_eq_ySeamPortEdge_of_yWrap (v j) hwrap,
            hedge]
        exact ⟨j, Finset.mem_filter.mpr ⟨hj, hwrap⟩, hcoord⟩
      · intro j hj
        exact ons_boundaryCoeff_mul_yWrapSign P (v j)
          (Finset.mem_filter.mp hj).2
    _ = ∑ x : ZMod L, ons_signedVerticalBoundary P (x, -1) := by
      apply Finset.sum_subset
      · simp [T]
      · intro x hx hnot
        have hnotF : ons_ySeamPortEdge L x ∉ F := by
          intro hmem
          apply hnot
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩
        have hz := ons_outgoingBoundaryCoeff_eq_zero_of_not_mem
          L F hF hhom (x, (-1 : ZMod L)) 1 (by
            simpa [ons_ySeamPortEdge] using hnotF)
        simpa [ons_outgoingBoundaryCoeff] using hz
    _ = 0 := ons_sum_signedVerticalBoundary_fixed_eq_zero P (-1)

theorem ons_simpleLoop_zeroHomology_winding_eq_zero
    {L n : ℕ} [Fact (2 < L)] [NeZero n]
    (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
    (hsite : Function.Injective (fun k ↦ (v k).1))
    (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2)
    (hF : ons_dartEdgeSet v ∈
      StatMech.Ising.evenSubgraphs (onsTorusGraph L))
    (hhom : ons_evenHomology L (ons_dartEdgeSet v) = 0) :
    (∑ k, ons_dirExponentX (v k).2) = 0 ∧
      (∑ k, ons_dirExponentY (v k).2) = 0 := by
  let F := ons_dartEdgeSet v
  let P := ons_zeroFluxPotential F
  let C := ons_loopBoundaryCoeff P v 0
  have hpred : ∀ k, ons_loopBoundaryCoeff P v k =
      ons_loopBoundaryCoeff P v (k - 1) := by
    intro k
    exact ons_loopBoundaryCoeff_pred v hvalid hsite hnu F hF rfl hhom k
  have hgeomConst : ∀ k, ons_loopBoundaryCoeff P v k = C := by
    exact ons_fin_pred_invariant (ons_loopBoundaryCoeff P v) hpred
  have hmatrixConst : ∀ j,
      ons_outgoingBoundaryCoeff P (v j).1 (v j).2 = C := by
    intro j
    have h := hgeomConst (-j)
    simpa [ons_loopBoundaryCoeff, ons_liftSite, ons_liftDir, C] using h
  have hC : C ≠ 0 := by
    have hedge : ons_portEdge L (v 0) ∈ F := by
      change ons_portEdge L (v 0) ∈ ons_dartEdgeSet v
      rw [ons_dartEdgeSet, Finset.mem_image]
      exact ⟨0, Finset.mem_univ _, rfl⟩
    have hn := ons_outgoingBoundaryCoeff_ne_zero_of_mem
      L F hF hhom (v 0).1 (v 0).2 hedge
    simpa [C, ons_loopBoundaryCoeff, P, ons_liftSite, ons_liftDir] using hn
  have hxWeighted := ons_sum_boundaryCoeff_mul_xWrapSign_eq_zero
    v hvalid hsite hnu F hF rfl hhom
  have hyWeighted := ons_sum_boundaryCoeff_mul_yWrapSign_eq_zero
    v hvalid hsite hnu F hF rfl hhom
  have hxWrap : (∑ j, ons_xWrapSign (v j)) = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left hC
    calc
      C * ∑ j, ons_xWrapSign (v j) =
          ∑ j, C * ons_xWrapSign (v j) := by
        rw [Finset.mul_sum]
      _ = ∑ j, ons_outgoingBoundaryCoeff P (v j).1 (v j).2 *
            ons_xWrapSign (v j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hmatrixConst j]
      _ = 0 := hxWeighted
  have hyWrap : (∑ j, ons_yWrapSign (v j)) = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left hC
    calc
      C * ∑ j, ons_yWrapSign (v j) =
          ∑ j, C * ons_yWrapSign (v j) := by
        rw [Finset.mul_sum]
      _ = ∑ j, ons_outgoingBoundaryCoeff P (v j).1 (v j).2 *
            ons_yWrapSign (v j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hmatrixConst j]
      _ = 0 := hyWeighted
  constructor
  · rw [ons_sum_dirExponentX_eq_wrap v hvalid, hxWrap, mul_zero]
  · rw [ons_sum_dirExponentY_eq_wrap v hvalid, hyWrap, mul_zero]

end StatMech.Onsager
