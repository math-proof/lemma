/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessOffCentre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriangularOffCentre.Part5
import Theorem.StatisticalMechanics.Code.OSSS.WiredDenominatorArithmetic
import Def.StatisticalMechanics.Code.FK.TriangularSharpnessOffCentre.Part3
open scoped BigOperators Classical
open Finset Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS RevealmentConstruction LindebergTree DecisionTree

open StatMech.OSSS.FiniteGraphBoundaryDifferential

open StatMech.OSSS.ReachBoxCrossing

open StatMech.OSSS.RevealmentTranslation

theorem triangularBox_root_neighbor_card_le_six (n : Nat) (hn : 1 ≤ n) :
    ((triangularBoxGraph n).neighborFinset (triangularBoxRoot n)).card ≤ 6 := by
  let candidates : Finset (TriangularBoxVertex n) :=
    Finset.univ.image (triangularBoxNeighbor n hn)
  have hsub : (triangularBoxGraph n).neighborFinset (triangularBoxRoot n) ⊆
      candidates := by
    intro y hy
    rw [SimpleGraph.mem_neighborFinset] at hy
    have hyAmbient : triangularGraph.Adj 0 y.1 := by
      simpa [triangularBoxGraph, triangularBoxRoot] using hy
    have hc := triangular_mem_candidates_of_adj hyAmbient
    rw [Finset.mem_image] at hc ⊢
    obtain ⟨ib, hib, hiy⟩ := hc
    exact ⟨ib, Finset.mem_univ _, Subtype.ext (by simpa [triangularBoxNeighbor] using hiy)⟩
  calc
    ((triangularBoxGraph n).neighborFinset (triangularBoxRoot n)).card ≤
        candidates.card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin 3 × Bool)).card := Finset.card_image_le
    _ = 6 := by decide

theorem triangularBox_root_degree_le_six (n : Nat) (hn : 1 ≤ n) :
    (triangularBoxGraph n).degree (triangularBoxRoot n) ≤ 6 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  exact triangularBox_root_neighbor_card_le_six n hn

theorem triangularInnerIncident_card_le_six (n : Nat) (hn : 1 ≤ n) :
    (reindexedOpenIncidentEdges
      (triangularBoxEdgeLE (by omega : n ≤ 2 * n))
      (triangularBoxEndU n) (triangularBoxEndV n)
      (triangularBoxRoot n)).card ≤ 6 := by
  let I := openIncidentEdges (triangularBoxEndU n) (triangularBoxEndV n)
    (triangularBoxRoot n)
  have himage : (reindexedOpenIncidentEdges
      (triangularBoxEdgeLE (by omega : n ≤ 2 * n))
      (triangularBoxEndU n) (triangularBoxEndV n)
      (triangularBoxRoot n)).card ≤ I.card := by
    unfold reindexedOpenIncidentEdges
    exact Finset.card_image_le
  have hsub : I.image (fun e => e.1) ⊆
      (triangularBoxGraph n).incidenceFinset (triangularBoxRoot n) := by
    intro edge hedge
    rw [Finset.mem_image] at hedge
    obtain ⟨e, heI, rfl⟩ := hedge
    rw [SimpleGraph.mem_incidenceFinset]
    refine ⟨e.2, ?_⟩
    have heo := (Finset.mem_filter.mp heI).2
    rw [triangularBox_end_coherent n e]
    rcases heo with heo | heo
    · simp [heo]
    · simp [heo]
  have hI : I.card ≤
      ((triangularBoxGraph n).neighborFinset (triangularBoxRoot n)).card := by
    have hincEq : (triangularBoxGraph n).incidenceFinset (triangularBoxRoot n) =
        ((triangularBoxGraph n).neighborFinset (triangularBoxRoot n)).image
          (fun w => s(triangularBoxRoot n, w)) := by
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
    have hinj : Set.InjOn (fun w : TriangularBoxVertex n =>
        s(triangularBoxRoot n, w))
        ↑((triangularBoxGraph n).neighborFinset (triangularBoxRoot n)) := by
      intro a ha b hb hab
      rcases Sym2.eq_iff.mp hab with hab | hab
      · exact hab.2
      · exact hab.2.trans hab.1
    calc
      I.card = (I.image (fun e => e.1)).card := by
        symm
        exact Finset.card_image_of_injective I Subtype.val_injective
      _ ≤ ((triangularBoxGraph n).incidenceFinset (triangularBoxRoot n)).card :=
        Finset.card_le_card hsub
      _ = ((triangularBoxGraph n).neighborFinset (triangularBoxRoot n)).card := by
        rw [hincEq]
        exact Finset.card_image_of_injOn hinj
  exact himage.trans (hI.trans (triangularBox_root_neighbor_card_le_six n hn))

theorem triangularInnerKappa_pos (n : Nat) (beta0 : Real) :
    0 < triangularInnerKappa n beta0 := by
  unfold triangularInnerKappa
  exact Finset.prod_pos fun e he => Real.exp_pos _

theorem exp_neg_pow_six_le_triangularInnerKappa
    (n : Nat) (hn : 1 ≤ n) (beta0 : Real) (hbeta0 : 0 ≤ beta0) :
    Real.exp (-beta0) ^ 6 ≤ triangularInnerKappa n beta0 := by
  unfold triangularInnerKappa
  rw [Finset.prod_const]
  exact pow_le_pow_of_le_one (Real.exp_pos _).le
    (Real.exp_le_one_iff.mpr (by linarith))
    (triangularInnerIncident_card_le_six n hn)

theorem triangular_outer_inner_one_sub_lower
    (n : Nat) (hn : 1 ≤ n) (q beta beta0 : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) (hbeta0 : beta ≤ beta0) :
    triangularInnerKappa n beta0 ≤
      1 - triangularOuterInnerTheta q beta n := by
  have hroot : triangularBoxRoot n ∉
      (triangularBoxShell n n : Set (TriangularBoxVertex n)) := by
    intro h
    have hnot := (Finset.mem_filter.mp h).2.2
    exact hnot (by
      intro i
      simp [triangularBoxRoot])
  have hmain := activeBC_reindexed_openCross_one_sub_lower
    (I := (triangularBoxGraph n).edgeSet)
    (triangularBoxGraph (2 * n)) (triangularBoxBoundaryGraph (2 * n))
    (fun _ => 1) (fun _ => by norm_num) q beta beta0 hq hbeta hbeta0
    (triangularBoxEdgeLE (by omega : n ≤ 2 * n))
    (triangularBoxEndU n) (triangularBoxEndV n) (triangularBoxRoot n)
    (triangularBoxShell n n : Set (TriangularBoxVertex n)) hroot
  have hn0 : n ≠ 0 := by omega
  simpa [triangularInnerKappa, triangularOuterInnerTheta, hn0] using hmain

theorem triangular_outer_inner_differential_linear_of_strict_comparison
    (n : Nat) (hn : 1 ≤ n) (q beta beta0 : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) (hbeta0 : beta ≤ beta0)
    (hcomp : ∀ x : TriangularBoxVertex n, ∀ k,
      k ∈ Finset.Icc 1 (n / 2) → 2 * k < n →
      triangularOuterCenteredConn n q beta x k ≤
        triangularOuterInnerTheta q beta k) :
    triangularInnerKappa n beta0 *
        (triangularOuterInnerTheta q beta n /
          (8 * triangularOuterInnerSig n q beta / (n : Real))) ≤
      triangularOuterInnerThetaPrime n q beta := by
  have htheta0 := triangularOuterInnerTheta_nonneg q beta hq hbeta n
  have hDpos : 0 < 8 * triangularOuterInnerSig n q beta / (n : Real) := by
    have hthetaZero : triangularOuterInnerTheta q beta 0 = 1 :=
      triangularOuterInnerTheta_zero q beta
    have hsig : 0 < triangularOuterInnerSig n q beta := by
      unfold triangularOuterInnerSig
      have hsingle : triangularOuterInnerTheta q beta 0 ≤
          ∑ k ∈ Finset.range n, triangularOuterInnerTheta q beta k := by
        apply Finset.single_le_sum
          (fun k _ => triangularOuterInnerTheta_nonneg q beta hq hbeta k)
        simpa using hn
      linarith
    have hnR : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
    positivity
  have hgap := triangular_outer_inner_one_sub_lower
    n hn q beta beta0 hq hbeta hbeta0
  have hlog := triangular_outer_inner_differential_sharp_of_strict_comparison
    n hn q beta hq hbeta hcomp
  calc
    triangularInnerKappa n beta0 *
        (triangularOuterInnerTheta q beta n /
          (8 * triangularOuterInnerSig n q beta / (n : Real))) =
      triangularOuterInnerTheta q beta n * triangularInnerKappa n beta0 /
        (8 * triangularOuterInnerSig n q beta / (n : Real)) := by ring
    _ ≤ triangularOuterInnerTheta q beta n *
        (1 - triangularOuterInnerTheta q beta n) /
          (8 * triangularOuterInnerSig n q beta / (n : Real)) :=
      (div_le_div_iff_of_pos_right hDpos).2
        (mul_le_mul_of_nonneg_left hgap htheta0)
    _ ≤ triangularOuterInnerThetaPrime n q beta := hlog

theorem triangular_outer_inner_hcov_sharp
    (n : Nat) (hn : 1 ≤ n) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) :
    let mu := FK.activeBCProb (triangularBoxGraph (2 * n))
      (triangularBoxBoundaryGraph (2 * n))
      (FK.betaParams (fun _ => 1) beta) q
    Lindeberg.mean mu (triangularInnerCrossInd n) *
        (1 - Lindeberg.mean mu (triangularInnerCrossInd n)) /
          (8 * triangularOuterInnerSig n q beta / (n : Real)) ≤
      ∑ e, Lindeberg.cov mu (triangularInnerCrossInd n) (Lindeberg.coord e) := by
  apply triangular_outer_inner_hcov_sharp_of_strict_comparison
    n hn q beta hq hbeta
  intro x k hk hstrict
  exact triangularOuterCenteredConn_le_theta_strict n k x
    (Finset.mem_Icc.mp hk).1 hstrict q beta hq hbeta

theorem triangular_outer_inner_differential_sharp
    (n : Nat) (hn : 1 ≤ n) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) :
    triangularOuterInnerTheta q beta n *
        (1 - triangularOuterInnerTheta q beta n) /
          (8 * triangularOuterInnerSig n q beta / (n : Real)) ≤
      triangularOuterInnerThetaPrime n q beta := by
  apply triangular_outer_inner_differential_sharp_of_strict_comparison
    n hn q beta hq hbeta
  intro x k hk hstrict
  exact triangularOuterCenteredConn_le_theta_strict n k x
    (Finset.mem_Icc.mp hk).1 hstrict q beta hq hbeta

theorem triangular_outer_inner_differential_linear
    (n : Nat) (hn : 1 ≤ n) (q beta beta0 : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) (hbeta0 : beta ≤ beta0) :
    triangularInnerKappa n beta0 *
        (triangularOuterInnerTheta q beta n /
          (8 * triangularOuterInnerSig n q beta / (n : Real))) ≤
      triangularOuterInnerThetaPrime n q beta := by
  apply triangular_outer_inner_differential_linear_of_strict_comparison
    n hn q beta beta0 hq hbeta hbeta0
  intro x k hk hstrict
  exact triangularOuterCenteredConn_le_theta_strict n k x
    (Finset.mem_Icc.mp hk).1 hstrict q beta hq hbeta

theorem triangularOuterInnerSig_pos
    (n : Nat) (hn : 1 ≤ n) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) :
    0 < triangularOuterInnerSig n q beta := by
  have hsingle : triangularOuterInnerTheta q beta 0 ≤
      ∑ k ∈ Finset.range n, triangularOuterInnerTheta q beta k := by
    apply Finset.single_le_sum
      (fun k _ => triangularOuterInnerTheta_nonneg q beta hq hbeta k)
    simpa using hn
  rw [triangularOuterInnerTheta_zero] at hsingle
  exact lt_of_lt_of_le zero_lt_one hsingle

end StatMech.FK.PeriodicPlanar
