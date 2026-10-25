/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedCorollaryReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamPinnedFieldAdapter.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMarkedSiteCorollary
import Def.StatisticalMechanics.Code.FrontierA.GrahamPinnedCorollaryReduction
open Finset
open scoped BigOperators
open Classical


namespace StatMech.FrontierA

open StatMech.ConfigSpace StatMech.Ising StatMech.Sharpness

open StatMech.Walls.VBG

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem grahamFieldFourPointLHS_anchor_eq
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hdiag : ∀ e ∈ E, ¬ e.IsDiag) {m i j k l : V}
    (him : i ≠ m) (hjm : j ≠ m) (hkm : k ≠ m) (hlm : l ≠ m) :
    grahamFieldFourPointLHS E (grahamAnchorCoupling J m)
        (grahamAnchorField E J m) i j k l =
      grahamUrsell4 E J i j k l := by
  unfold grahamFieldFourPointLHS grahamUrsell4
  rw [grahamAnchor_fourPoint_eq E J hdiag him hjm hkm hlm,
    grahamAnchor_twoPoint_eq E J hdiag him hjm,
    grahamAnchor_twoPoint_eq E J hdiag hkm hlm,
    grahamAnchor_twoPoint_eq E J hdiag him hkm,
    grahamAnchor_twoPoint_eq E J hdiag hjm hlm,
    grahamAnchor_twoPoint_eq E J hdiag him hlm,
    grahamAnchor_twoPoint_eq E J hdiag hjm hkm]


theorem grahamFieldFourPointRHS_anchor_eq
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hdiag : ∀ e ∈ E, ¬ e.IsDiag) {m i j k l : V}
    (him : i ≠ m) (hjm : j ≠ m) (hkm : k ≠ m) (hlm : l ≠ m) :
    grahamFieldFourPointRHS E (grahamAnchorCoupling J m)
        (grahamAnchorField E J m) i j k l =
      grahamCorrectedRHS E J i j k l m := by
  unfold grahamFieldFourPointRHS grahamFieldCovariance
  rw [grahamAnchor_onePoint_eq E J hdiag him,
    grahamAnchor_onePoint_eq E J hdiag hjm,
    grahamAnchor_onePoint_eq E J hdiag hkm,
    grahamAnchor_onePoint_eq E J hdiag hlm,
    grahamAnchor_twoPoint_eq E J hdiag him hkm,
    grahamAnchor_twoPoint_eq E J hdiag hjm hkm,
    grahamAnchor_twoPoint_eq E J hdiag him hlm,
    grahamAnchor_twoPoint_eq E J hdiag hkm hlm]
  unfold grahamCorrectedRHS grahamLeadingTerm grahamKCorrection
    grahamICorrection grahamBridgeGap
  rw [grahamTwoPoint_comm E J m k, grahamTwoPoint_comm E J m l]
  ring


theorem grahamCorrectedBound_iff_anchorField
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hdiag : ∀ e ∈ E, ¬ e.IsDiag) {m i j k l : V}
    (him : i ≠ m) (hjm : j ≠ m) (hkm : k ≠ m) (hlm : l ≠ m) :
    grahamUrsell4 E J i j k l <= grahamCorrectedRHS E J i j k l m ↔
      grahamFieldFourPointLHS E (grahamAnchorCoupling J m)
          (grahamAnchorField E J m) i j k l <=
        grahamFieldFourPointRHS E (grahamAnchorCoupling J m)
          (grahamAnchorField E J m) i j k l := by
  rw [grahamFieldFourPointLHS_anchor_eq E J hdiag him hjm hkm hlm,
    grahamFieldFourPointRHS_anchor_eq E J hdiag him hjm hkm hlm]


theorem grahamUrsell4_pair_rotate
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (i j k l : V) :
    grahamUrsell4 E J i j k l = grahamUrsell4 E J k l i j := by
  have hfour : grahamFourPoint E J i j k l =
      grahamFourPoint E J k l i j := by
    unfold grahamFourPoint grahamFourSupport
    rw [symmDiff_comm]
  unfold grahamUrsell4
  rw [hfour, grahamTwoPoint_comm E J i j,
    grahamTwoPoint_comm E J k l,
    grahamTwoPoint_comm E J k i,
    grahamTwoPoint_comm E J l j,
    grahamTwoPoint_comm E J k j,
    grahamTwoPoint_comm E J l i]
  ring

theorem grahamUrsell4_swap_last
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (i j k l : V) :
    grahamUrsell4 E J i j k l = grahamUrsell4 E J i j l k := by
  have hfour : grahamFourPoint E J i j k l =
      grahamFourPoint E J i j l k := by
    unfold grahamFourPoint grahamFourSupport grahamPairSupport
    rw [symmDiff_comm ({k} : Finset V) {l}]
  unfold grahamUrsell4
  rw [hfour, grahamTwoPoint_comm E J k l,
    grahamTwoPoint_comm E J i k, grahamTwoPoint_comm E J i l,
    grahamTwoPoint_comm E J j k, grahamTwoPoint_comm E J j l]
  ring

theorem grahamUrsell4_cycle
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (i j k l : V) :
    grahamUrsell4 E J i j k l = grahamUrsell4 E J j k l i := by
  have hfour : grahamFourPoint E J i j k l =
      grahamFourPoint E J j k l i := by
    rw [grahamFourPoint_eq_expJ, grahamFourPoint_eq_expJ]
    congr 1
    funext s
    ring
  unfold grahamUrsell4
  rw [hfour, grahamTwoPoint_comm E J i j,
    grahamTwoPoint_comm E J i k, grahamTwoPoint_comm E J i l,
    grahamTwoPoint_comm E J j k, grahamTwoPoint_comm E J j l,
    grahamTwoPoint_comm E J k l]
  ring


theorem grahamCorrectedBound_aux_eq_first
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hdiag : ∀ e ∈ E, ¬ e.IsDiag) (hJ : ∀ e, 0 <= J e)
    (i j k l : V) :
    grahamUrsell4 E J i j k l <= grahamCorrectedRHS E J i j k l i := by
  have hmarked := grahamMarkedSite_four_point_edgeFinset
    E J hdiag hJ j k l i
  have hsign := grahamCorrectedRHS_le_leading E J
    (fun e he => hJ e) j k l i i
  have hU : grahamUrsell4 E J i j k l =
      grahamUrsell4 E J j k l i := grahamUrsell4_cycle E J i j k l
  have htarget : grahamCorrectedRHS E J i j k l i =
      grahamLeadingTerm E J j k l i i := by
    unfold grahamCorrectedRHS grahamLeadingTerm grahamKCorrection
      grahamICorrection grahamBridgeGap
    simp [grahamTwoPoint_comm E J]
  rw [hU, htarget]
  exact hmarked.trans hsign


theorem grahamCorrectedBound_aux_eq_second
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hdiag : ∀ e ∈ E, ¬ e.IsDiag) (hJ : ∀ e, 0 <= J e)
    (i j k l : V) :
    grahamUrsell4 E J i j k l <= grahamCorrectedRHS E J i j k l j := by
  have hmarked := grahamMarkedSite_four_point_edgeFinset
    E J hdiag hJ k l i j
  rw [← grahamUrsell4_pair_rotate E J i j k l] at hmarked
  have hrhs : grahamCorrectedRHS E J k l i j j =
      grahamCorrectedRHS E J i j k l j := by
    unfold grahamCorrectedRHS grahamLeadingTerm grahamKCorrection
      grahamICorrection grahamBridgeGap
    simp [grahamTwoPoint_comm E J]
    ring
  rwa [hrhs] at hmarked


theorem grahamCorrectedBound_aux_eq_third
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hdiag : ∀ e ∈ E, ¬ e.IsDiag) (hJ : ∀ e, 0 <= J e)
    (i j k l : V) :
    grahamUrsell4 E J i j k l <= grahamCorrectedRHS E J i j k l k := by
  have hmarked := grahamMarkedSite_four_point_edgeFinset
    E J hdiag hJ i j l k
  have hsign := grahamCorrectedRHS_le_leading E J
    (fun e he => hJ e) i j l k k
  have hU : grahamUrsell4 E J i j k l =
      grahamUrsell4 E J i j l k := grahamUrsell4_swap_last E J i j k l
  have htarget : grahamCorrectedRHS E J i j k l k =
      grahamLeadingTerm E J i j l k k := by
    unfold grahamCorrectedRHS grahamLeadingTerm grahamKCorrection
      grahamICorrection grahamBridgeGap
    simp [grahamTwoPoint_comm E J]
  rw [hU, htarget]
  exact hmarked.trans hsign


theorem grahamCorrectedBound_of_aux_mem_marks
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hdiag : ∀ e ∈ E, ¬ e.IsDiag) (hJ : ∀ e, 0 <= J e)
    (i j k l m : V) (hm : m = i ∨ m = j ∨ m = k ∨ m = l) :
    grahamUrsell4 E J i j k l <= grahamCorrectedRHS E J i j k l m := by
  rcases hm with hmi | hmj | hmk | hml
  · subst m
    exact grahamCorrectedBound_aux_eq_first E J hdiag hJ i j k l
  · subst m
    exact grahamCorrectedBound_aux_eq_second E J hdiag hJ i j k l
  · subst m
    exact grahamCorrectedBound_aux_eq_third E J hdiag hJ i j k l
  · subst m
    exact grahamMarkedSite_four_point_edgeFinset E J hdiag hJ i j k l

end StatMech.FrontierA
