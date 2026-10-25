/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedAnchor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedCandidates.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryToggleWinding.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedOpenBoundaryDependence
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem seamTrace_eq_sum_range
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialDart R.medialTorus) (n : Nat) :
    fkRectMedialBoundaryPrimalSeamTrace R pairing d n =
      ∑ i ∈ Finset.range n,
        fkRectMedialBoundaryPrimalSeamIncrement R pairing
          ((fkMedialBoundaryStep pairing)^[i] d) := by
  induction n generalizing d with
  | zero => simp [fkRectMedialBoundaryPrimalSeamTrace]
  | succ n ih =>
      rw [fkRectMedialBoundaryPrimalSeamTrace, ih,
        Finset.sum_range_succ']
      have htail :
          (∑ i ∈ Finset.range n,
            fkRectMedialBoundaryPrimalSeamIncrement R pairing
              ((fkMedialBoundaryStep pairing)^[i]
                (fkMedialBoundaryStep pairing d))) =
          ∑ i ∈ Finset.range n,
            fkRectMedialBoundaryPrimalSeamIncrement R pairing
              ((fkMedialBoundaryStep pairing)^[i + 1] d) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Function.iterate_succ_apply]
      rw [htail]
      simp only [Function.iterate_zero_apply]
      exact add_comm _ _


theorem fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d) =
      fkRectBlackBoundaryCycleClassWinding R
        (fkRectConfigurationToMedialPairing R omega) d := by
  classical
  let pairing := fkRectConfigurationToMedialPairing R omega
  let sigma := fkMedialBlackBoundaryPerm pairing
  let l := fkRectBlackOrbitList pairing d
  let f : FKMedialBlackDart R.medialTorus → Int × Int :=
    fkRectBlackBoundaryWeight R pairing
  have hdSupport : d ∈ sigma.support := by
    rw [Equiv.Perm.mem_support]
    exact fkMedialBlackBoundaryPerm_apply_ne pairing d
  rw [fkRectBlackBoundaryPrimalCycleWalk_winding]
  change fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 l.length = _
  rw [seamTrace_eq_sum_range]
  have hsum :
      (∑ i ∈ Finset.range l.length,
        fkRectMedialBoundaryPrimalSeamIncrement R pairing
          ((fkMedialBoundaryStep pairing)^[i] d.1)) =
        ∑ i ∈ Finset.range l.length, f ((sigma^[i]) d) := by
    apply Finset.sum_congr rfl
    intro i hi
    unfold f fkRectBlackBoundaryWeight
    rw [fkMedialBlackBoundaryPerm_iterate_val]
  rw [hsum]
  change (∑ i ∈ Finset.range l.length, f ((sigma^[i]) d)) = _
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    (∑ i : Fin l.length, f ((sigma^[i.val]) d)) =
        (l.map f).sum := by
          rw [← List.sum_ofFn]
          have hlist :
              List.ofFn (fun i : Fin l.length ↦ f ((sigma^[i.val]) d)) =
                l.map f := by
            rw [← List.ofFn_getElem_eq_map l f]
            congr 1
            funext i
            apply congrArg f
            simpa [l, sigma, List.get_eq_getElem] using
              (fkRectBlackOrbitList_get pairing d i).symm
          rw [hlist]
    _ = ∑ x ∈ l.toFinset, f x := by
      exact (List.sum_toFinset f (by
        simpa [l, sigma] using Equiv.Perm.nodup_toList sigma d)).symm
    _ = fkRectBlackBoundaryCycleClassWinding R pairing d := by
      unfold fkRectBlackBoundaryCycleClassWinding
        permCycleClassWeightSum
      rw [← Finset.sum_filter]
      congr 1
      ext x
      simp only [List.mem_toFinset, Finset.mem_filter, Finset.mem_univ,
        true_and]
      change x ∈ sigma.toList d ↔ sigma.SameCycle d x
      rw [Equiv.Perm.mem_toList_iff]
      simp [hdSupport]


theorem fkRectMedialBoundaryPrimalOrbitWalk_winding_eq_nsmul_blackCycle
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R omega d.1) =
      permOrbitVisitCount
          (fkMedialBoundaryStep
            (fkRectConfigurationToMedialPairing R omega)) d.1 d.1 •
        fkRectWalkWinding R
          (fkRectBlackBoundaryPrimalCycleWalk R omega d) := by
  rw [fkRectMedialBoundaryPrimalOrbitWalk_winding_eq_visitCount_nsmul,
    fkRectBoundaryCycleClassWinding_eq_black,
    fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass]


theorem
    fkRectMedialBoundaryPrimalOrbitWalk_winding_ne_zero_of_componentTurn_eq_zero
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus)
    (hturn : FKMedialTurningFiber.canonicalComponentTurn
      (fkRectConfigurationToMedialPairing R omega)
      ((fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk d) =
        0) :
    fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R omega d) ≠ (0, 0) := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  have blackCase (b : FKMedialBlackDart R.medialTorus)
      (hbturn : FKMedialTurningFiber.canonicalComponentTurn pairing
        ((fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk b.1) =
          0) :
      fkRectWalkWinding R
          (fkRectMedialBoundaryPrimalOrbitWalk R omega b.1) ≠ (0, 0) := by
    have hdisp := fkRectBlackOrbitDisplacement_ne_zero_of_turn_eq_zero
      R pairing
      ((fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk b.1)
      b rfl hbturn
    have hprimitive :=
      fkRectBlackBoundaryPrimalCycleWalk_winding_ne_zero_of_displacement
        R omega b hdisp
    rw [fkRectMedialBoundaryPrimalOrbitWalk_winding_eq_nsmul_blackCycle]
    let m := permOrbitVisitCount (fkMedialBoundaryStep pairing) b.1 b.1
    have hm : 0 < m := permOrbitVisitCount_self_pos _ _
    intro hzero
    apply hprimitive
    have hfirst := congrArg Prod.fst hzero
    have hsecond := congrArg Prod.snd hzero
    simp only [Prod.smul_fst, Prod.smul_snd, nsmul_eq_mul,
      Prod.fst_zero, Prod.snd_zero] at hfirst hsecond
    have hm0 : (m : Int) ≠ 0 := by exact_mod_cast hm.ne'
    apply Prod.ext
    · exact (mul_eq_zero.mp hfirst).resolve_left hm0
    · exact (mul_eq_zero.mp hsecond).resolve_left hm0
  by_cases hd : fkMedialCheckerColor d = false
  · let b : FKMedialBlackDart R.medialTorus := ⟨d, hd⟩
    exact blackCase b (by simpa [pairing, b] using hturn)
  · have hdtrue : fkMedialCheckerColor d = true :=
      Bool.eq_true_of_not_eq_false hd
    let e := fkMedialLocalMate pairing d
    have heblack : fkMedialCheckerColor e = false := by
      rw [show e = fkMedialLocalMate pairing d from rfl,
        fkMedialCheckerColor_localMate_eq_not, hdtrue]
      rfl
    let b : FKMedialBlackDart R.medialTorus := ⟨e, heblack⟩
    have heComponent : (fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk
        e = (fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk d := by
      apply SimpleGraph.ConnectedComponent.sound
      exact (fkMedial_reachable_localMate pairing d).symm
    have hbturn : FKMedialTurningFiber.canonicalComponentTurn pairing
        ((fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk b.1) =
          0 := by
      change FKMedialTurningFiber.canonicalComponentTurn pairing
          ((fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk e) = 0
      rw [heComponent]
      exact hturn
    have hb := blackCase b hbturn
    intro hzero
    apply hb
    change fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R omega e) = (0, 0)
    rw [show e = fkMedialLocalMate pairing d from rfl,
      fkRectMedialBoundaryPrimalOrbitWalk_winding_localMate, hzero]
    simp


theorem fkRect_boundaryOrbit_winding_dependent_of_openWalk_configuration
    (R : FKRectTorus) (omega : R.Configuration) {x : R.Vertex}
    (w : (fkRectOpenGraph R omega).Walk x x)
    (d : FKMedialDart R.medialTorus) :
    ¬ FKRectWindingIndependent
      (fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R omega d))
      (fkRectWalkWinding R w) := by
  generalize hF : fkRectOpenEdges R omega = F
  have hconfig : fkRectConfigurationOfEdges R F = omega := by
    rw [← hF]
    exact fkRectConfigurationOfEdges_openEdges R omega
  clear hF
  cases hconfig
  exact fkRect_boundaryOrbit_winding_dependent_of_openWalk R F w d


theorem fkRectClosedOpenWalk_verticalWinding_eq_zero_of_remainder
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    {x : R.Vertex} (w : (fkRectOpenGraph R omega).Walk x x) :
    (fkRectWalkWinding R w).2 = 0 := by
  let d := fkRectZeroTurnRemainderBlackDart R omega C
  let m := permOrbitVisitCount
    (fkMedialBoundaryStep
      (fkRectConfigurationToMedialPairing R omega)) d.1 d.1
  have hm : 0 < m := permOrbitVisitCount_self_pos _ _
  have hd1 := fkRectZeroTurnRemainderBlackDart_winding_fst_ne_zero R omega C
  have hd2 := fkRectZeroTurnRemainderBlackDart_winding_snd_eq_zero R omega C
  have hdep :=
    fkRect_boundaryOrbit_winding_dependent_of_openWalk_configuration
      R omega w d.1
  rw [fkRectMedialBoundaryPrimalOrbitWalk_winding_eq_nsmul_blackCycle
    R omega d] at hdep
  unfold FKRectWindingIndependent at hdep
  push Not at hdep
  simp only [Prod.smul_fst, Prod.smul_snd] at hdep
  simp only [nsmul_eq_mul] at hdep
  change (fkRectWalkWinding R
    (fkRectBlackBoundaryPrimalCycleWalk R omega d)).1 ≠ 0 at hd1
  change (fkRectWalkWinding R
    (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2 = 0 at hd2
  have hm0 : (m : Int) ≠ 0 := by exact_mod_cast hm.ne'
  rw [hd2] at hdep
  simp only [mul_zero, zero_mul, sub_zero] at hdep
  rcases mul_eq_zero.mp hdep with hma | hw
  · exact ((mul_ne_zero hm0 hd1) hma).elim
  · exact hw


theorem not_fkRectHasNet_of_zeroTurnRemainder
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    ¬ FKRectHasNet R omega := by
  rintro ⟨x, p, q, hpq⟩
  have hp := fkRectClosedOpenWalk_verticalWinding_eq_zero_of_remainder
    R omega C p
  have hq := fkRectClosedOpenWalk_verticalWinding_eq_zero_of_remainder
    R omega C q
  apply hpq
  rw [hp, hq]
  ring


theorem fkRectMedialBoundaryPrimalOrbitWalk_verticalWinding_eq_zero_of_remainder
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (d : FKMedialDart R.medialTorus) :
    (fkRectWalkWinding R
      (fkRectMedialBoundaryPrimalOrbitWalk R omega d)).2 = 0 := by
  let b := fkRectZeroTurnRemainderBlackDart R omega C
  let w := fkRectBlackBoundaryPrimalCycleWalk R omega b
  have hb1 :=
    fkRectZeroTurnRemainderBlackDart_winding_fst_ne_zero R omega C
  have hb2 :=
    fkRectZeroTurnRemainderBlackDart_winding_snd_eq_zero R omega C
  have hdep :=
    fkRect_boundaryOrbit_winding_dependent_of_openWalk_configuration
      R omega w d
  unfold FKRectWindingIndependent at hdep
  push Not at hdep
  change (fkRectWalkWinding R w).1 ≠ 0 at hb1
  change (fkRectWalkWinding R w).2 = 0 at hb2
  rw [hb2] at hdep
  simp only [mul_zero, zero_sub] at hdep
  have hmul :
      (fkRectWalkWinding R
          (fkRectMedialBoundaryPrimalOrbitWalk R omega d)).2 *
        (fkRectWalkWinding R w).1 = 0 := by
    linarith
  exact (mul_eq_zero.mp hmul).resolve_right hb1


theorem fkRectBlackBoundaryPrimalCycleWalk_verticalWinding_eq_zero_of_remainder
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (d : FKMedialBlackDart R.medialTorus) :
    (fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2 = 0 := by
  have horbit :=
    fkRectMedialBoundaryPrimalOrbitWalk_verticalWinding_eq_zero_of_remainder
      R omega C d.1
  rw [fkRectMedialBoundaryPrimalOrbitWalk_winding_eq_nsmul_blackCycle]
    at horbit
  let m := permOrbitVisitCount
    (fkMedialBoundaryStep
      (fkRectConfigurationToMedialPairing R omega)) d.1 d.1
  have hmul : (m : Int) *
      (fkRectWalkWinding R
        (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2 = 0 := by
    simpa only [m, Prod.smul_snd, nsmul_eq_mul] using horbit
  have hm0 : (m : Int) ≠ 0 := by
    have hpos := permOrbitVisitCount_self_pos
      (fkMedialBoundaryStep
        (fkRectConfigurationToMedialPairing R omega)) d.1
    exact_mod_cast hpos.ne'
  exact (mul_eq_zero.mp hmul).resolve_left hm0


end
end StatMech.FrontierD
