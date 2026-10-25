/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKernelCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part13
import Instance.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part3


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

noncomputable def killedChoiceFirstHitFamilyEquiv
    (R t : Nat) (p q : IsingLeapfrogBox R) (level : Int) :
    IsingLeapfrogKilledChoiceFirstHitFamily R t p q level ≃
      SurvivingFirstHitFamily R (isingLeapfrogBoxInt p) level t
        (isingLeapfrogBoxInt q) where
  toFun z := by
    let w := z.1.1
    let split := z.1.2
    have hsteps := firstHitSplit_steps z.2
    have hfirst := firstHitSplit_firstHit z.2
    have hvalid : z.1.2.Valid := by
      unfold IsingDiagonalWalkHitSplit.Valid
      rw [hsteps]
      exact isingLeapfrogChoiceSteps_valid w.1
    have hlength : z.1.2.steps.length = t := by
      rw [hsteps]
      simpa [isingLeapfrogChoiceSteps] using w.2.1
    have hendpoint : z.1.2.endpoint = isingLeapfrogBoxInt q := by
      unfold endpoint
      rw [hsteps]
      have hrun := w.2.2.1.run_boxInt_eq_endpoint R p w.1
      rw [w.2.2.2] at hrun
      exact hrun.symm
    have hstays : StaysInOpenBox R (isingLeapfrogBoxInt p) z.1.2.steps := by
      rw [hsteps]
      exact w.2.2.1.staysInOpenBox R p w.1
    exact ⟨⟨split, hfirst, hvalid, hlength, hendpoint⟩, hstays⟩
  invFun z := by
    let bs := isingLeapfrogEncodeSteps z.1.1.steps
    have hvalid := z.1.2.2.1
    have hdecode := choiceSteps_encodeSteps_of_valid z.1.1.steps hvalid
    have hkilled := killedChoiceValid_encodeSteps_of_stays R p z.1.1.steps
      hvalid z.2
    have hrunBox : isingLeapfrogChoiceRun R p bs = q := by
      have hrun := hkilled.run_boxInt_eq_endpoint R p bs
      rw [hdecode] at hrun
      have hend := z.1.2.2.2.2
      unfold endpoint at hend
      rw [hend] at hrun
      exact isingLeapfrogBoxInt_injective hrun
    let w : IsingLeapfrogKilledChoicePathFamily R t p q :=
      ⟨bs, by simpa [bs, isingLeapfrogEncodeSteps] using z.1.2.2.2.1,
        hkilled, hrunBox⟩
    refine ⟨⟨w, z.1.1⟩, ?_⟩
    rw [show isingLeapfrogChoiceSteps w.1 = z.1.1.steps by
      exact hdecode]
    exact firstHitSplit_eq_some z.1.1 z.1.2.1
  left_inv z := by
    rcases z with ⟨⟨w, split⟩, hz⟩
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      change isingLeapfrogEncodeSteps split.steps = w.1
      rw [firstHitSplit_steps hz, encodeSteps_choiceSteps]
    · rfl
  right_inv z := by
    apply Subtype.ext
    rfl

end
end StatMech.Universality
