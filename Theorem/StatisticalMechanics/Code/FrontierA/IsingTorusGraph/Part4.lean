/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusStationarity
import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSimon.Part8
import Theorem.StatisticalMechanics.Code.Sharpness.HighTempPlusBox.Part5
import Def.StatisticalMechanics.Code.FrontierA.IsingTorusGraph.Part3
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Sharpness

variable {d k : Nat}

theorem isingTorus_bond_sum_eq
    (sigma : ConfigSpace (IsingDyadicTorus d k)) :
    (∑ e ∈ (isingTorusGraph d k).edgeFinset, bond sigma e) =
      ∑ x : IsingDyadicTorus d k, ∑ i : Fin d,
        spin sigma x * spin sigma (x + isingTorusStep i) := by
  rw [show (∑ e ∈ (isingTorusGraph d k).edgeFinset, bond sigma e) =
      ∑ e : (isingTorusGraph d k).edgeFinset, bond sigma e by
        rw [← Finset.sum_attach]
        simp]
  rw [← (isingTorusIndexedEdgeEquiv (d := d) (k := k)).sum_comp]
  rw [Fintype.sum_prod_type]
  rfl

theorem isingTorusDirichlet_spin_eq
    (sigma : ConfigSpace (IsingDyadicTorus d k)) :
    isingTorusDirichlet (isingTorusSpinField sigma) =
      2 * Fintype.card (IsingDyadicTorus d k) * d -
        2 * ∑ e ∈ (isingTorusGraph d k).edgeFinset, bond sigma e := by
  rw [isingTorus_bond_sum_eq]
  unfold isingTorusDirichlet isingTorusDirichletBilinear
  simp only [isingTorusSpinField]
  calc
    (∑ x : IsingDyadicTorus d k, ∑ i : Fin d,
        (spin sigma x - spin sigma (x + isingTorusStep i)) *
          (spin sigma x - spin sigma (x + isingTorusStep i))) =
      ∑ x : IsingDyadicTorus d k, ∑ i : Fin d,
        (2 - 2 * (spin sigma x *
          spin sigma (x + isingTorusStep i))) := by
            apply Finset.sum_congr rfl
            intro x _
            apply Finset.sum_congr rfl
            intro i _
            calc
              (spin sigma x - spin sigma (x + isingTorusStep i)) *
                  (spin sigma x - spin sigma (x + isingTorusStep i)) =
                spin sigma x * spin sigma x +
                  spin sigma (x + isingTorusStep i) *
                    spin sigma (x + isingTorusStep i) -
                  2 * (spin sigma x *
                    spin sigma (x + isingTorusStep i)) := by ring
              _ = 2 - 2 * (spin sigma x *
                    spin sigma (x + isingTorusStep i)) := by
                rw [spin_sq, spin_sq]
                ring
    _ = 2 * Fintype.card (IsingDyadicTorus d k) * d -
        2 * ∑ x : IsingDyadicTorus d k, ∑ i : Fin d,
          spin sigma x * spin sigma (x + isingTorusStep i) := by
            simp_rw [Finset.sum_sub_distrib, Finset.mul_sum]
            simp
            ring

theorem spinProd_sourcePair_eq_twoSpin
    (sigma : ConfigSpace (IsingDyadicTorus d k))
    (x y : IsingDyadicTorus d k) :
    spinProd (sourcePair x y) sigma = spin sigma x * spin sigma y := by
  by_cases hxy : x = y
  · subst y
    rw [sourcePair_self, spinProd_empty, spin_sq]
  · rw [sourcePair_eq_pair hxy]
    unfold spinProd
    rw [Finset.prod_pair hxy]

theorem isingTorus_zero_weight_eq_graph_weight
    (beta : Real) (sigma : ConfigSpace (IsingDyadicTorus d k)) :
    Real.exp (-(beta / 2) *
        isingTorusDirichlet (isingTorusSpinField sigma)) =
      Real.exp (-beta *
          (Fintype.card (IsingDyadicTorus d k) : Real) * d) *
        isingWeight (isingTorusGraph d k) beta 0 sigma := by
  rw [isingTorusDirichlet_spin_eq]
  unfold isingWeight hamiltonian
  simp only [zero_mul, sub_zero]
  rw [← Real.exp_add]
  congr 1
  push_cast
  ring

theorem isingTorusShiftedPartition_zero_eq_graph
    (beta : Real) :
    isingTorusShiftedPartition (d := d) (k := k) beta 0 =
      Real.exp (-beta *
          (Fintype.card (IsingDyadicTorus d k) : Real) * d) *
        isingZ (isingTorusGraph d k) beta 0 := by
  unfold isingTorusShiftedPartition isingZ
  simp only [Pi.zero_apply, Pi.add_apply, add_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro sigma _
  exact isingTorus_zero_weight_eq_graph_weight beta sigma


theorem isingTorusTwoPoint_eq_twoPointJ
    (beta : Real) (x y : IsingDyadicTorus d k) :
    isingTorusTwoPoint beta x y =
      twoPointJ (isingTorusGraph d k) beta (fun _ => 1) x y := by
  unfold twoPointJ
  rw [expectationJ_one_eq_isingExpectation]
  unfold isingTorusTwoPoint isingExpectation isingProb
  rw [isingTorusShiftedPartition_zero_eq_graph]
  simp_rw [spinProd_sourcePair_eq_twoSpin]
  have hscale : Real.exp (-beta *
      (Fintype.card (IsingDyadicTorus d k) : Real) * d) ≠ 0 :=
    (Real.exp_pos _).ne'
  have hnum :
      (∑ sigma : ConfigSpace (IsingDyadicTorus d k),
          Real.exp (-(beta / 2) *
              isingTorusDirichlet (isingTorusSpinField sigma)) *
            spin sigma x * spin sigma y) =
        Real.exp (-beta *
            (Fintype.card (IsingDyadicTorus d k) : Real) * d) *
          ∑ sigma : ConfigSpace (IsingDyadicTorus d k),
            spin sigma x * spin sigma y *
              Real.exp (beta *
                ∑ e ∈ (isingTorusGraph d k).edgeFinset,
                  bond sigma e) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro sigma _
    rw [isingTorus_zero_weight_eq_graph_weight]
    unfold isingWeight hamiltonian
    simp only [zero_mul, sub_zero]
    ring
  change
    (∑ sigma : ConfigSpace (IsingDyadicTorus d k),
        Real.exp (-(beta / 2) *
            isingTorusDirichlet (isingTorusSpinField sigma)) *
          spin sigma x * spin sigma y) /
      (Real.exp (-beta *
          (Fintype.card (IsingDyadicTorus d k) : Real) * d) *
        isingZ (isingTorusGraph d k) beta 0) =
      ∑ sigma : ConfigSpace (IsingDyadicTorus d k),
        isingWeight (isingTorusGraph d k) beta 0 sigma /
          isingZ (isingTorusGraph d k) beta 0 *
            (spin sigma x * spin sigma y)
  rw [hnum]
  rw [mul_div_mul_left _ _ hscale]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro sigma _
  unfold isingWeight hamiltonian
  simp only [zero_mul, sub_zero]
  ring

theorem isingTorusTwoPoint_eq_twoPointJ_unitEdge
    (beta : Real) (x y : IsingDyadicTorus d k) :
    isingTorusTwoPoint beta x y =
      twoPointJ (isingTorusGraph d k) beta
        (unitEdgeCoupling (isingTorusGraph d k)) x y := by
  rw [isingTorusTwoPoint_eq_twoPointJ]
  symm
  apply twoPointJ_congr_on_edges
  intro e he
  exact unitEdgeCoupling_edgeFinset (isingTorusGraph d k) he

theorem isingTorusTwoPoint_le_one
    (beta : Real) (x y : IsingDyadicTorus d k) :
    isingTorusTwoPoint beta x y ≤ 1 := by
  unfold isingTorusTwoPoint
  have hZ := isingTorusShiftedPartition_zero_pos
    (d := d) (k := k) beta
  apply (div_le_one hZ).2
  calc
    (∑ sigma : ConfigSpace (IsingDyadicTorus d k),
        Real.exp (-(beta / 2) *
            isingTorusDirichlet (isingTorusSpinField sigma)) *
          isingTorusSpinField sigma x *
            isingTorusSpinField sigma y) ≤
      ∑ sigma : ConfigSpace (IsingDyadicTorus d k),
        Real.exp (-(beta / 2) *
          isingTorusDirichlet (isingTorusSpinField sigma)) := by
            apply Finset.sum_le_sum
            intro sigma _
            have hx : isingTorusSpinField sigma x = 1 ∨
                isingTorusSpinField sigma x = -1 := by
              unfold isingTorusSpinField spin
              split <;> simp
            have hy : isingTorusSpinField sigma y = 1 ∨
                isingTorusSpinField sigma y = -1 := by
              unfold isingTorusSpinField spin
              split <;> simp
            rcases hx with hx | hx <;> rcases hy with hy | hy <;>
              rw [hx, hy] <;> simp <;> positivity
    _ = isingTorusShiftedPartition (d := d) (k := k) beta 0 := by
      unfold isingTorusShiftedPartition
      simp

theorem isingTorusTwoPoint_sum_translate
    (beta : Real) (y : IsingDyadicTorus d k) :
    (∑ z : IsingDyadicTorus d k, isingTorusTwoPoint beta y z) =
      ∑ z : IsingDyadicTorus d k, isingTorusTwoPoint beta 0 z := by
  let e : IsingDyadicTorus d k ≃ IsingDyadicTorus d k :=
    Equiv.addRight (-y)
  have hsum := e.sum_comp
    (fun z : IsingDyadicTorus d k => isingTorusTwoPoint beta 0 z)
  calc
    (∑ z : IsingDyadicTorus d k, isingTorusTwoPoint beta y z) =
        ∑ z : IsingDyadicTorus d k, isingTorusTwoPoint beta 0 (z - y) := by
          apply Finset.sum_congr rfl
          intro z _
          exact isingTorusTwoPoint_eq_origin_displacement y z beta
    _ = ∑ z : IsingDyadicTorus d k, isingTorusTwoPoint beta 0 z := by
      simpa only [e, sub_eq_add_neg] using hsum


theorem isingTorus_susceptibility_le_of_simon
    (beta : Real) (hbeta : 0 ≤ beta)
    (S : Finset (IsingDyadicTorus d k)) (hzero : 0 ∈ S)
    (hphi : simonConst S
        (simonWeightPair (isingTorusGraph d k) beta
          (unitEdgeCoupling (isingTorusGraph d k)) S 0)
        (Finset.univ \ S) < 1) :
    (∑ z : IsingDyadicTorus d k, isingTorusTwoPoint beta 0 z) ≤
      (S.card : Real) / (1 - simonConst S
        (simonWeightPair (isingTorusGraph d k) beta
          (unitEdgeCoupling (isingTorusGraph d k)) S 0)
        (Finset.univ \ S)) := by
  let tau : IsingDyadicTorus d k → IsingDyadicTorus d k → Real :=
    fun x y => twoPointJ (isingTorusGraph d k) beta
      (unitEdgeCoupling (isingTorusGraph d k)) x y
  let weight : IsingDyadicTorus d k → IsingDyadicTorus d k → Real :=
    simonWeightPair (isingTorusGraph d k) beta
      (unitEdgeCoupling (isingTorusGraph d k)) S 0
  let boundary : Finset (IsingDyadicTorus d k) := Finset.univ \ S
  have hSL : SimonLieb tau 0 S weight boundary := by
    exact twoPointJ_simonLieb_finite (isingTorusGraph d k) beta
      (unitEdgeCoupling (isingTorusGraph d k)) hbeta
      (unitEdgeCoupling_nonneg (isingTorusGraph d k)) S 0 hzero
  let chi : Real := ∑ z : IsingDyadicTorus d k, tau 0 z
  have hchi : 0 ≤ chi :=
    Finset.sum_nonneg (fun z _ => hSL.τ_nonneg 0 z)
  have htranslate (y : IsingDyadicTorus d k) :
      (∑ z : IsingDyadicTorus d k, tau y z) = chi := by
    dsimp only [tau, chi]
    simp_rw [← isingTorusTwoPoint_eq_twoPointJ_unitEdge]
    exact isingTorusTwoPoint_sum_translate beta y
  have houtside : ∀ y ∈ boundary,
      (∑ z ∈ (Finset.univ : Finset (IsingDyadicTorus d k)) \ S,
          tau y z) ≤ chi := by
    intro y hy
    calc
      (∑ z ∈ (Finset.univ : Finset (IsingDyadicTorus d k)) \ S,
          tau y z) ≤ ∑ z : IsingDyadicTorus d k, tau y z := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · exact Finset.sdiff_subset
            · intro z hz _
              exact hSL.τ_nonneg y z
      _ = chi := htranslate y
  have hSbound :
      (∑ z ∈ (Finset.univ : Finset (IsingDyadicTorus d k)) ∩ S,
          tau 0 z) ≤ (S.card : Real) := by
    calc
      (∑ z ∈ (Finset.univ : Finset (IsingDyadicTorus d k)) ∩ S,
          tau 0 z) ≤
          ∑ _z ∈ (Finset.univ : Finset (IsingDyadicTorus d k)) ∩ S,
            (1 : Real) := by
              apply Finset.sum_le_sum
              intro z hz
              dsimp only [tau]
              rw [← isingTorusTwoPoint_eq_twoPointJ_unitEdge]
              exact isingTorusTwoPoint_le_one beta 0 z
      _ = (S.card : Real) := by simp
  have hself : chi ≤ (S.card : Real) +
      simonConst S weight boundary * chi := by
    have h := susceptibility_self_consistent_sl tau 0 S weight boundary
      hSL (Finset.univ : Finset (IsingDyadicTorus d k)) chi
      houtside hchi hSbound
    simpa [chi] using h
  have hbound := susceptibility_solve chi (S.card : Real)
    (simonConst S weight boundary) hchi (by simpa [weight, boundary] using hphi)
    hself
  dsimp only [chi, tau] at hbound
  simp_rw [← isingTorusTwoPoint_eq_twoPointJ_unitEdge] at hbound
  simpa [weight, boundary] using hbound

end StatMech.FrontierA
