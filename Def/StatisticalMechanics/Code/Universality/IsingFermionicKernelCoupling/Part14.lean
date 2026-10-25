/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKernelCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part13
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part9


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def killedChoiceNoHitAllProjection
    (R t : Nat) (p : IsingLeapfrogBox R) (level : Int) :
    IsingLeapfrogKilledChoiceNoHitAll R t p level →
      IsingHorizontalNoHitFamily t (isingLeapfrogBoxInt p).1 level ×
        {ys : List Bool // ys.length = t} := fun w =>
  ⟨⟨w.1.1.map Prod.fst, by simpa using w.1.2.1, by
      intro k hk hhit
      have hne := firstHitSplit_none_endpoint_fst_ne w.2 k (by
        simpa [isingLeapfrogChoiceSteps, w.1.2.1] using hk)
      apply hne
      calc
        (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
            ((isingLeapfrogChoiceSteps w.1.1).take k)).1 =
            (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
              (isingLeapfrogChoiceSteps (w.1.1.take k))).1 := by
                simp [isingLeapfrogChoiceSteps, List.map_take]
        _ = lineFreeEndpoint (isingLeapfrogBoxInt p).1
            ((w.1.1.take k).map Prod.fst) :=
          (lineFreeEndpoint_choiceHorizontal (w.1.1.take k)
            (isingLeapfrogBoxInt p)).symm
        _ = level := by simpa [List.map_take] using hhit⟩,
    ⟨w.1.1.map Prod.snd, by simpa using w.1.2.1⟩⟩

end
end StatMech.Universality
