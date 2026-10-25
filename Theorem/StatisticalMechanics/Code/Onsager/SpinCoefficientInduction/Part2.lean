/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinCoefficientInduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.SpinWeightedBase
import Def.StatisticalMechanics.Code.Onsager.SpinCoefficientInduction.Part2


namespace StatMech.Onsager

open Matrix BigOperators StatMech.Ising

theorem ons_weightedRootIdentity_of_edgeCoefficient
    (L : ℕ) [Fact (2 < L)]
    (hcoeff : ons_weightedEdgeCoefficientIdentity L) :
    ons_weightedRootIdentity L := by
  intro a b weight q hq hweight hsmall
  have hind : ∀ S : Finset (Sym2 (ZMod L × ZMod L)),
      S ⊆ (onsTorusGraph L).edgeFinset →
      ons_detWalkRoot
          (ons_KWmatWeightedPhase L (ons_restrictEdgeWeight weight S)
            ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) =
        ons_weightedSpinCharacterSum L (ons_restrictEdgeWeight weight S) a b := by
    intro S hsub
    induction S using Finset.induction with
    | empty =>
        simpa [ons_restrictEdgeWeight] using ons_weightedRoot_zero L a b
    | @insert edge S hedge ih =>
        have hSsub : S ⊆ (onsTorusGraph L).edgeFinset := by
          intro f hf
          exact hsub (Finset.mem_insert_of_mem hf)
        have hedgeG : edge ∈ (onsTorusGraph L).edgeFinset :=
          hsub (Finset.mem_insert_self edge S)
        obtain ⟨e, he⟩ := ons_torusEdge_eq_portEdge L hedgeG
        let wI := ons_restrictEdgeWeight weight (insert edge S)
        have hwI : ∀ f, ‖wI f‖ ≤ q :=
          norm_ons_restrictEdgeWeight_le weight _ q hq hweight
        have hzeroW :
            ons_scaleEdgeWeight wI (ons_portEdge L e) 0 =
              ons_restrictEdgeWeight weight S := by
          rw [he]
          exact ons_scale_restrict_insert_zero weight S edge hedge
        have honeW :
            ons_scaleEdgeWeight wI (ons_portEdge L e) 1 = wI := by
          rw [he]
          exact ons_scale_restrict_insert_one weight S edge
        have hstep := ons_weightedRoot_eq_spin_scaleEdge_of_coefficient
          L wI a b q hq hwI 1 (by norm_num) e hsmall
          (by simpa only [hzeroW] using ih hSsub)
          (hcoeff a b wI q hq hwI hsmall e)
        simpa only [honeW, wI] using hstep
  have hfull := hind (onsTorusGraph L).edgeFinset Finset.Subset.rfl
  rw [ons_KWmatWeightedPhase_restrict_edgeFinset,
    ons_weightedSpinCharacterSum_restrict_edgeFinset] at hfull
  exact hfull

end StatMech.Onsager
