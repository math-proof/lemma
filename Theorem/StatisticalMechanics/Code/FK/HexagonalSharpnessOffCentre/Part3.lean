/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessOffCentre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.HexagonalOffCentre.Part5
import Theorem.StatisticalMechanics.Code.OSSS.WiredDenominatorArithmetic
import Def.StatisticalMechanics.Code.FK.HexagonalSharpnessOffCentre.Part3
open scoped BigOperators Classical
open Finset Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS RevealmentConstruction LindebergTree DecisionTree

open StatMech.OSSS.FiniteGraphBoundaryDifferential

open StatMech.OSSS.ReachBoxCrossing

open StatMech.OSSS.RevealmentTranslation

theorem hexagonalBox_root_neighbor_card_le_six (n : Nat) (hn : 1 ≤ n) :
    ((hexagonalBoxGraph n).neighborFinset (hexagonalBoxRoot n)).card ≤ 6 := by
  let candidates : Finset (HexagonalBoxVertex n) :=
    Finset.univ.image (hexagonalBoxNeighbor n hn)
  have hsub : (hexagonalBoxGraph n).neighborFinset (hexagonalBoxRoot n) ⊆
      candidates := by
    intro y hy
    rw [SimpleGraph.mem_neighborFinset] at hy
    have hyAmbient : hexagonalGraph.Adj (0, false) y.1 := by
      simpa [hexagonalBoxGraph, hexagonalBoxRoot] using hy
    have hc := hexagonal_mem_candidates_of_adj hyAmbient
    rw [Finset.mem_image] at hc ⊢
    obtain ⟨ib, hib, hiy⟩ := hc
    exact ⟨ib, Finset.mem_univ _,
      Subtype.ext (by simpa [hexagonalBoxNeighbor] using hiy)⟩
  calc
    ((hexagonalBoxGraph n).neighborFinset (hexagonalBoxRoot n)).card ≤
        candidates.card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin 3)).card := Finset.card_image_le
    _ ≤ 6 := by decide

theorem hexagonalBox_root_degree_le_six (n : Nat) (hn : 1 ≤ n) :
    (hexagonalBoxGraph n).degree (hexagonalBoxRoot n) ≤ 6 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  exact hexagonalBox_root_neighbor_card_le_six n hn

theorem hexagonalInnerIncident_card_le_six (n : Nat) (hn : 1 ≤ n) :
    (reindexedOpenIncidentEdges
      (hexagonalBoxEdgeLE (by omega : n ≤ 2 * n))
      (hexagonalBoxEndU n) (hexagonalBoxEndV n)
      (hexagonalBoxRoot n)).card ≤ 6 := by
  let I := openIncidentEdges (hexagonalBoxEndU n) (hexagonalBoxEndV n)
    (hexagonalBoxRoot n)
  have himage : (reindexedOpenIncidentEdges
      (hexagonalBoxEdgeLE (by omega : n ≤ 2 * n))
      (hexagonalBoxEndU n) (hexagonalBoxEndV n)
      (hexagonalBoxRoot n)).card ≤ I.card := by
    unfold reindexedOpenIncidentEdges
    exact Finset.card_image_le
  have hsub : I.image (fun e => e.1) ⊆
      (hexagonalBoxGraph n).incidenceFinset (hexagonalBoxRoot n) := by
    intro edge hedge
    rw [Finset.mem_image] at hedge
    obtain ⟨e, heI, rfl⟩ := hedge
    rw [SimpleGraph.mem_incidenceFinset]
    refine ⟨e.2, ?_⟩
    have heo := (Finset.mem_filter.mp heI).2
    rw [hexagonalBox_end_coherent n e]
    rcases heo with heo | heo
    · simp [heo]
    · simp [heo]
  have hI : I.card ≤
      ((hexagonalBoxGraph n).neighborFinset (hexagonalBoxRoot n)).card := by
    have hincEq : (hexagonalBoxGraph n).incidenceFinset (hexagonalBoxRoot n) =
        ((hexagonalBoxGraph n).neighborFinset (hexagonalBoxRoot n)).image
          (fun w => s(hexagonalBoxRoot n, w)) := by
      ext edge
      induction edge using Sym2.inductionOn with
      | _ a b =>
          simp only [SimpleGraph.mem_incidenceFinset,
            SimpleGraph.mk'_mem_incidenceSet_iff, Finset.mem_image,
            SimpleGraph.mem_neighborFinset]
          constructor
          · rintro ⟨hab, rfl | rfl⟩
            · exact ⟨b, hab, rfl⟩
            · exact ⟨a, hab.symm, Sym2.eq_swap⟩
          · rintro ⟨w, hw, heq⟩
            rcases Sym2.eq_iff.mp heq with ⟨hra, hwb⟩ | ⟨hrb, hwa⟩
            · subst a
              subst b
              exact ⟨hw, by simp⟩
            · subst b
              subst a
              exact ⟨hw.symm, by simp⟩
    have hinj : Set.InjOn (fun w : HexagonalBoxVertex n =>
        s(hexagonalBoxRoot n, w))
        ↑((hexagonalBoxGraph n).neighborFinset (hexagonalBoxRoot n)) := by
      intro a ha b hb hab
      rcases Sym2.eq_iff.mp hab with hab | hab
      · exact hab.2
      · exact hab.2.trans hab.1
    calc
      I.card = (I.image (fun e => e.1)).card := by
        symm
        exact Finset.card_image_of_injective I Subtype.val_injective
      _ ≤ ((hexagonalBoxGraph n).incidenceFinset (hexagonalBoxRoot n)).card :=
        Finset.card_le_card hsub
      _ = ((hexagonalBoxGraph n).neighborFinset (hexagonalBoxRoot n)).card := by
        rw [hincEq]
        exact Finset.card_image_of_injOn hinj
  exact himage.trans (hI.trans (hexagonalBox_root_neighbor_card_le_six n hn))

theorem hexagonalInnerKappa_pos (n : Nat) (beta0 : Real) :
    0 < hexagonalInnerKappa n beta0 := by
  unfold hexagonalInnerKappa
  exact Finset.prod_pos fun e he => Real.exp_pos _

theorem exp_neg_pow_six_le_hexagonalInnerKappa
    (n : Nat) (hn : 1 ≤ n) (beta0 : Real) (hbeta0 : 0 ≤ beta0) :
    Real.exp (-beta0) ^ 6 ≤ hexagonalInnerKappa n beta0 := by
  unfold hexagonalInnerKappa
  rw [Finset.prod_const]
  exact pow_le_pow_of_le_one (Real.exp_pos _).le
    (Real.exp_le_one_iff.mpr (by linarith))
    (hexagonalInnerIncident_card_le_six n hn)

theorem hexagonal_outer_inner_one_sub_lower
    (n : Nat) (hn : 1 ≤ n) (q beta beta0 : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) (hbeta0 : beta ≤ beta0) :
    hexagonalInnerKappa n beta0 ≤
      1 - hexagonalOuterInnerTheta q beta n := by
  have hroot : hexagonalBoxRoot n ∉
      (hexagonalBoxShell n n : Set (HexagonalBoxVertex n)) := by
    intro h
    have hnot := (Finset.mem_filter.mp h).2.2
    exact hnot (by
      intro i
      simp [hexagonalBoxRoot])
  have hmain := activeBC_reindexed_openCross_one_sub_lower
    (I := (hexagonalBoxGraph n).edgeSet)
    (hexagonalBoxGraph (2 * n)) (hexagonalBoxBoundaryGraph (2 * n))
    (fun _ => 1) (fun _ => by norm_num) q beta beta0 hq hbeta hbeta0
    (hexagonalBoxEdgeLE (by omega : n ≤ 2 * n))
    (hexagonalBoxEndU n) (hexagonalBoxEndV n) (hexagonalBoxRoot n)
    (hexagonalBoxShell n n : Set (HexagonalBoxVertex n)) hroot
  have hn0 : n ≠ 0 := by omega
  simpa [hexagonalInnerKappa, hexagonalOuterInnerTheta, hn0] using hmain

theorem hexagonal_outer_inner_differential_linear_of_strict_comparison
    (n : Nat) (hn : 1 ≤ n) (q beta beta0 : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) (hbeta0 : beta ≤ beta0)
    (hcomp : ∀ x : HexagonalBoxVertex n, ∀ k,
      k ∈ Finset.Icc 1 (n / 2) → 2 * k < n →
      hexagonalOuterCenteredConn n q beta x k ≤
        hexagonalOuterInnerTheta q beta k) :
    hexagonalInnerKappa n beta0 *
        (hexagonalOuterInnerTheta q beta n /
          (8 * hexagonalOuterInnerSig n q beta / (n : Real))) ≤
      hexagonalOuterInnerThetaPrime n q beta := by
  have htheta0 := hexagonalOuterInnerTheta_nonneg q beta hq hbeta n
  have hDpos : 0 < 8 * hexagonalOuterInnerSig n q beta / (n : Real) := by
    have hthetaZero : hexagonalOuterInnerTheta q beta 0 = 1 :=
      hexagonalOuterInnerTheta_zero q beta
    have hsig : 0 < hexagonalOuterInnerSig n q beta := by
      unfold hexagonalOuterInnerSig
      have hsingle : hexagonalOuterInnerTheta q beta 0 ≤
          ∑ k ∈ Finset.range n, hexagonalOuterInnerTheta q beta k := by
        apply Finset.single_le_sum
          (fun k _ => hexagonalOuterInnerTheta_nonneg q beta hq hbeta k)
        simpa using hn
      linarith
    have hnR : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
    positivity
  have hgap := hexagonal_outer_inner_one_sub_lower
    n hn q beta beta0 hq hbeta hbeta0
  have hlog := hexagonal_outer_inner_differential_sharp_of_strict_comparison
    n hn q beta hq hbeta hcomp
  calc
    hexagonalInnerKappa n beta0 *
        (hexagonalOuterInnerTheta q beta n /
          (8 * hexagonalOuterInnerSig n q beta / (n : Real))) =
      hexagonalOuterInnerTheta q beta n * hexagonalInnerKappa n beta0 /
        (8 * hexagonalOuterInnerSig n q beta / (n : Real)) := by ring
    _ ≤ hexagonalOuterInnerTheta q beta n *
        (1 - hexagonalOuterInnerTheta q beta n) /
          (8 * hexagonalOuterInnerSig n q beta / (n : Real)) :=
      (div_le_div_iff_of_pos_right hDpos).2
        (mul_le_mul_of_nonneg_left hgap htheta0)
    _ ≤ hexagonalOuterInnerThetaPrime n q beta := hlog

theorem hexagonal_outer_inner_hcov_sharp
    (n : Nat) (hn : 1 ≤ n) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) :
    let mu := FK.activeBCProb (hexagonalBoxGraph (2 * n))
      (hexagonalBoxBoundaryGraph (2 * n))
      (FK.betaParams (fun _ => 1) beta) q
    Lindeberg.mean mu (hexagonalInnerCrossInd n) *
        (1 - Lindeberg.mean mu (hexagonalInnerCrossInd n)) /
          (8 * hexagonalOuterInnerSig n q beta / (n : Real)) ≤
      ∑ e, Lindeberg.cov mu (hexagonalInnerCrossInd n) (Lindeberg.coord e) := by
  apply hexagonal_outer_inner_hcov_sharp_of_strict_comparison
    n hn q beta hq hbeta
  intro x k hk hstrict
  exact hexagonalOuterCenteredConn_le_theta_strict n k x
    (Finset.mem_Icc.mp hk).1 hstrict q beta hq hbeta

theorem hexagonal_outer_inner_differential_sharp
    (n : Nat) (hn : 1 ≤ n) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) :
    hexagonalOuterInnerTheta q beta n *
        (1 - hexagonalOuterInnerTheta q beta n) /
          (8 * hexagonalOuterInnerSig n q beta / (n : Real)) ≤
      hexagonalOuterInnerThetaPrime n q beta := by
  apply hexagonal_outer_inner_differential_sharp_of_strict_comparison
    n hn q beta hq hbeta
  intro x k hk hstrict
  exact hexagonalOuterCenteredConn_le_theta_strict n k x
    (Finset.mem_Icc.mp hk).1 hstrict q beta hq hbeta

theorem hexagonal_outer_inner_differential_linear
    (n : Nat) (hn : 1 ≤ n) (q beta beta0 : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) (hbeta0 : beta ≤ beta0) :
    hexagonalInnerKappa n beta0 *
        (hexagonalOuterInnerTheta q beta n /
          (8 * hexagonalOuterInnerSig n q beta / (n : Real))) ≤
      hexagonalOuterInnerThetaPrime n q beta := by
  apply hexagonal_outer_inner_differential_linear_of_strict_comparison
    n hn q beta beta0 hq hbeta hbeta0
  intro x k hk hstrict
  exact hexagonalOuterCenteredConn_le_theta_strict n k x
    (Finset.mem_Icc.mp hk).1 hstrict q beta hq hbeta

theorem hexagonalOuterInnerSig_pos
    (n : Nat) (hn : 1 ≤ n) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) :
    0 < hexagonalOuterInnerSig n q beta := by
  have hsingle : hexagonalOuterInnerTheta q beta 0 ≤
      ∑ k ∈ Finset.range n, hexagonalOuterInnerTheta q beta k := by
    apply Finset.single_le_sum
      (fun k _ => hexagonalOuterInnerTheta_nonneg q beta hq hbeta k)
    simpa using hn
  rw [hexagonalOuterInnerTheta_zero] at hsingle
  exact lt_of_lt_of_le zero_lt_one hsingle

end StatMech.FK.PeriodicPlanar
