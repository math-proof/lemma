/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointEscape.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicOrderedEndpointConvolution
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTailEndpointRace
import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure.Part3


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem firstVerticalBoundaryTime_of_sourceBoundary
    (R t : Nat) (p q : IsingLeapfrogBox R) (level : Int)
    (w : IsingSourceFailureOutputAtFamily R t p q level)
    (j : Nat) (hjT : j <= t)
    (hminimal : forall l, l < j -> ¬ isingLeapfrogBoxBoundary R
      (isingLeapfrogChoiceRun R p (w.1.1.1.take l)))
    (hrun : isingLeapfrogBoxInt
        (isingLeapfrogChoiceRun R p (w.1.1.1.take j)) =
      isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
        (isingLeapfrogChoiceSteps (w.1.1.1.take j)))
    (hprefixQ : isingLeapfrogChoiceRun R p (w.1.1.1.take j) = q)
    (hqVertical : q.2.1 = 0 \/ q.2.1 = R) :
    firstVerticalBoundaryTimeEndpointFailure R
      (isingLeapfrogBoxInt p).2 (w.1.1.1.map Prod.snd) = j := by
  apply firstVerticalBoundaryTimeEndpointFailure_eq
  · simpa [w.1.1.2] using hjT
  · rw [← List.map_take, lineFreeEndpoint_choiceVertical_full]
    have hry := congrArg Prod.snd hrun
    rw [hprefixQ] at hry
    rcases hqVertical with hq0 | hqR
    · left
      rw [← hry]
      unfold isingLeapfrogBoxInt
      dsimp
      exact_mod_cast hq0
    · right
      rw [← hry]
      unfold isingLeapfrogBoxInt
      dsimp
      exact_mod_cast hqR
  · intro l hl
    have hexec : IsingLeapfrogChoiceExecValid R p (w.1.1.1.take l) := by
      intro r hr
      rw [List.length_take] at hr
      have hrl : r < l := by omega
      simpa [List.take_take, Nat.min_eq_left hrl.le] using
        hminimal r (hrl.trans hl)
    have hrunl := choiceExecValid_run_boxInt_eq_endpoint R p
      (w.1.1.1.take l) hexec
    have hry := congrArg Prod.snd hrunl
    change ((isingLeapfrogChoiceRun R p (w.1.1.1.take l)).2.1 : Int) =
      (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
        (isingLeapfrogChoiceSteps (w.1.1.1.take l))).2 at hry
    have hline : lineFreeEndpoint (isingLeapfrogBoxInt p).2
        ((w.1.1.1.map Prod.snd).take l) =
        ((isingLeapfrogChoiceRun R p (w.1.1.1.take l)).2.1 : Int) := by
      rw [← List.map_take, lineFreeEndpoint_choiceVertical_full, ← hry]
    constructor
    · intro hzero
      apply hminimal l hl
      unfold isingLeapfrogBoxBoundary
      right; right; left
      rw [hline] at hzero
      exact_mod_cast hzero
    · intro hR
      apply hminimal l hl
      unfold isingLeapfrogBoxBoundary
      right; right; right
      rw [hline] at hR
      have : (isingLeapfrogChoiceRun R p
          (w.1.1.1.take l)).2.1 = R := by exact_mod_cast hR
      omega

theorem exists_sourceFailureOutput_transverseWitness
    (R level rho t : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hρ : 0 < rho) (hbottom : rho <= p.2.1)
    (htop : p.2.1 + rho <= R)
    (hqVertical : q.2.1 = 0 \/ q.2.1 = R)
    (w : IsingSourceFailureOutputAtFamily R t p q (level : Int)) :
    exists z : IsingTransverseRaceWitnessFamily rho t (level : Int),
      transverseRaceWitnessValue rho t (level : Int) z = w.1.1 /\
        (z.1 : Nat) <= firstVerticalBoundaryTimeEndpointFailure R
          (isingLeapfrogBoxInt p).2 (w.1.1.1.map Prod.snd) := by
  have hstartLt : (isingLeapfrogBoxInt p).1 < (level : Int) := by omega
  rcases sourceFailure_boundary_data R t p (level : Int) hstartLt w.1 with
    ⟨split, j, hsplit, hj, hb, hminimal, hxlt, hrun⟩
  have hjT : j <= t := by
    have hlen := congrArg List.length (firstHitSplit_steps hsplit)
    simp [IsingDiagonalWalkHitSplit.steps, isingLeapfrogChoiceSteps,
      w.1.1.2] at hlen
    omega
  have hprefixQ : isingLeapfrogChoiceRun R p (w.1.1.1.take j) = q := by
    have hdecomp : w.1.1.1 = w.1.1.1.take j ++ w.1.1.1.drop j :=
      (List.take_append_drop j w.1.1.1).symm
    have hfull : isingLeapfrogChoiceRun R p w.1.1.1 =
        isingLeapfrogChoiceRun R p (w.1.1.1.take j) := by
      calc
        _ = isingLeapfrogChoiceRun R p
            (w.1.1.1.take j ++ w.1.1.1.drop j) := by rw [← hdecomp]
        _ = isingLeapfrogChoiceRun R
            (isingLeapfrogChoiceRun R p (w.1.1.1.take j))
              (w.1.1.1.drop j) := isingLeapfrogChoiceRun_append_full ..
        _ = _ :=
          isingLeapfrogChoiceRun_of_boundary_endpointFailure R _ hb _
    exact hfull.symm.trans w.2
  rcases hqVertical with hqBottom | hqTop
  · have hyEnd : (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
        (isingLeapfrogChoiceSteps (w.1.1.1.take j))).2 <=
          (isingLeapfrogBoxInt p).2 - rho := by
      have hyrun := congrArg Prod.snd hrun
      rw [hprefixQ] at hyrun
      change ((q.2.1 : Nat) : Int) =
        (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
          (isingLeapfrogChoiceSteps (w.1.1.1.take j))).2 at hyrun
      have hbottomInt : (rho : Int) <= (isingLeapfrogBoxInt p).2 := by
        unfold isingLeapfrogBoxInt
        dsimp
        exact_mod_cast hbottom
      rw [show ((q.2.1 : Nat) : Int) = 0 by exact_mod_cast hqBottom] at hyrun
      omega
    rcases exists_vertical_barrier_prefix_lower rho hρ
      (isingLeapfrogBoxInt p) (w.1.1.1.take j) (by
        unfold isingLeapfrogBoxInt
        dsimp
        exact_mod_cast hbottom) hyEnd with ⟨s, hs, heq⟩
    have hsJ : s <= j := le_trans hs (List.length_take_le ..)
    rcases transverseWitness_of_barrier_exists rho t (level : Int) hρ
      (isingLeapfrogBoxInt p) (by omega) w.1.1 split hsplit j hj
      ⟨s, hsJ, Or.inl (by
        simpa [List.take_take, Nat.min_eq_left hsJ] using heq)⟩ with
      ⟨z, hz, hzj⟩
    refine ⟨z, hz, ?_⟩
    rw [firstVerticalBoundaryTime_of_sourceBoundary R t p q
      (level : Int) w j hjT hminimal hrun hprefixQ (Or.inl hqBottom)]
    exact hzj
  · have hyEnd : (isingLeapfrogBoxInt p).2 + rho <=
        (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
          (isingLeapfrogChoiceSteps (w.1.1.1.take j))).2 := by
      have hyrun := congrArg Prod.snd hrun
      rw [hprefixQ] at hyrun
      change ((q.2.1 : Nat) : Int) =
        (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
          (isingLeapfrogChoiceSteps (w.1.1.1.take j))).2 at hyrun
      have htopInt : (isingLeapfrogBoxInt p).2 + (rho : Int) <= R := by
        unfold isingLeapfrogBoxInt
        dsimp
        exact_mod_cast htop
      rw [show ((q.2.1 : Nat) : Int) = R by exact_mod_cast hqTop] at hyrun
      omega
    rcases exists_vertical_barrier_prefix rho hρ
      (isingLeapfrogBoxInt p) (w.1.1.1.take j) j (by simp [hjT]) (by
        unfold isingLeapfrogBoxInt
        dsimp
        exact_mod_cast hbottom) hyEnd with ⟨s, hs, heq⟩
    have hsJ : s <= j := le_trans hs (List.length_take_le ..)
    rcases transverseWitness_of_barrier_exists rho t (level : Int) hρ
      (isingLeapfrogBoxInt p) (by omega) w.1.1 split hsplit j hj
      ⟨s, hsJ, Or.inr (by
        simpa [List.take_take, Nat.min_eq_left hsJ] using heq)⟩ with
      ⟨z, hz, hzj⟩
    refine ⟨z, hz, ?_⟩
    rw [firstVerticalBoundaryTime_of_sourceBoundary R t p q
      (level : Int) w j hjT hminimal hrun hprefixQ (Or.inr hqTop)]
    exact hzj

theorem sourceEndpointRaceTarget_eq
    (R level rho t : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hqVertical : q.2.1 = 0 \/ q.2.1 = R)
    (w : IsingSourceFailureOutputAtFamily R t p q (level : Int))
    (z : IsingTransverseRaceWitnessFamily rho t (level : Int))
    (hz : transverseRaceWitnessValue rho t (level : Int) z = w.1.1)
    (hmark : (z.1 : Nat) <= firstVerticalBoundaryTimeEndpointFailure R
      (isingLeapfrogBoxInt p).2 (w.1.1.1.map Prod.snd)) :
    lineFreeEndpoint ((level : Int) - 1) z.2.1.1 =
      sourceEndpointRaceTarget R t rho p q z.1 z.2.2.1 z.2.2.2 := by
  have hstartLt : (isingLeapfrogBoxInt p).1 < (level : Int) := by omega
  rcases sourceFailure_boundary_data R t p (level : Int) hstartLt w.1 with
    ⟨split, j, hsplit, hj, hb, hminimal, hxlt, hrun⟩
  have hjT : j <= t := by
    have hlen := congrArg List.length (firstHitSplit_steps hsplit)
    simp [IsingDiagonalWalkHitSplit.steps, isingLeapfrogChoiceSteps,
      w.1.1.2] at hlen
    omega
  have hprefixQ : isingLeapfrogChoiceRun R p (w.1.1.1.take j) = q := by
    have hdecomp : w.1.1.1 = w.1.1.1.take j ++ w.1.1.1.drop j :=
      (List.take_append_drop j w.1.1.1).symm
    have hfull : isingLeapfrogChoiceRun R p w.1.1.1 =
        isingLeapfrogChoiceRun R p (w.1.1.1.take j) := by
      calc
        _ = isingLeapfrogChoiceRun R p
            (w.1.1.1.take j ++ w.1.1.1.drop j) := by rw [← hdecomp]
        _ = isingLeapfrogChoiceRun R
            (isingLeapfrogChoiceRun R p (w.1.1.1.take j))
              (w.1.1.1.drop j) := isingLeapfrogChoiceRun_append_full ..
        _ = _ :=
          isingLeapfrogChoiceRun_of_boundary_endpointFailure R _ hb _
    exact hfull.symm.trans w.2
  have hstop := firstVerticalBoundaryTime_of_sourceBoundary R t p q
    (level : Int) w j hjT hminimal hrun hprefixQ hqVertical
  have hmarkJ : (z.1 : Nat) <= j := by simpa [hstop] using hmark
  have hvalue : (z.2.1.1.zip z.2.2.1.1) ++ z.2.2.2.1 = w.1.1.1 := by
    exact congrArg (fun u : IsingLeapfrogChoiceStringFamily t => u.1) hz
  have hxyLength : z.2.1.1.length = z.2.2.1.1.length := by
    rw [z.2.1.2.1, z.2.2.1.2.1]
  have hxFull : z.2.1.1 ++ z.2.2.2.1.map Prod.fst =
      w.1.1.1.map Prod.fst := by
    have hx := congrArg (List.map Prod.fst) hvalue
    simpa [List.map_append,
      map_fst_zip_of_length_eq_endpointFailure _ _ hxyLength] using hx
  have hyFull : z.2.2.1.1 ++ z.2.2.2.1.map Prod.snd =
      w.1.1.1.map Prod.snd := by
    have hy := congrArg (List.map Prod.snd) hvalue
    simpa [List.map_append,
      map_snd_zip_of_length_eq_endpointFailure _ _ hxyLength] using hy
  have hstopY : firstVerticalBoundaryTimeEndpointFailure R
      (isingLeapfrogBoxInt p).2
        (z.2.2.1.1 ++ z.2.2.2.1.map Prod.snd) = j := by
    rw [hyFull]
    exact hstop
  have hxPrefix : (w.1.1.1.map Prod.fst).take j =
      z.2.1.1 ++ (z.2.2.2.1.map Prod.fst).take (j - (z.1 : Nat)) := by
    rw [← hxFull, List.take_append]
    simp [z.2.1.2.1, hmarkJ]
  have hrawX : lineFreeEndpoint (isingLeapfrogBoxInt p).1
      ((w.1.1.1.map Prod.fst).take j) = (isingLeapfrogBoxInt q).1 := by
    rw [← List.map_take, lineFreeEndpoint_choiceHorizontal_full]
    have hx := congrArg Prod.fst hrun
    rw [hprefixQ] at hx
    exact hx.symm
  have hstartX : (isingLeapfrogBoxInt p).1 = (level : Int) - 1 := by omega
  rw [hstartX, hxPrefix, lineFreeEndpoint_append_endpointFailure] at hrawX
  have htranslate := lineFreeEndpoint_translate
    ((z.2.2.2.1.map Prod.fst).take (j - (z.1 : Nat))) 0
      (lineFreeEndpoint ((level : Int) - 1) z.2.1.1)
  unfold sourceEndpointRaceTarget
  dsimp only
  rw [hstopY]
  rw [htranslate] at hrawX
  linarith

end
end StatMech.Universality
