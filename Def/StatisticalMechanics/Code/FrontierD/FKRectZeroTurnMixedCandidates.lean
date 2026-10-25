/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnMixedCandidates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.FKRectMedialDualShift.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedAnnulusCharge
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectZeroTurnRemainderDualBoundaryCycleWalk
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    (fkRectOpenGraph R (fkRectDualConfigurationEquiv R omega)).Walk
      (fkRectMedialDartPrimalLabel R
        (fkRectMedialDualShiftDart R
          (fkRectZeroTurnRemainderBlackDart R omega C).1))
      (fkRectMedialDartPrimalLabel R
        (fkRectMedialDualShiftDart R
          (fkRectZeroTurnRemainderBlackDart R omega C).1)) := by
  let d := fkRectZeroTurnRemainderBlackDart R omega C
  let pairing := fkRectConfigurationToMedialPairing R omega
  let dualPairing := fkRectConfigurationToMedialPairing R
    (fkRectDualConfigurationEquiv R omega)
  let n := (fkRectBlackOrbitList pairing d).length
  let p := fkRectMedialBoundaryPrimalTrace R
    (fkRectDualConfigurationEquiv R omega)
    (fkRectMedialDualShiftDart R d.1) n
  have hblack : (fkMedialBlackBoundaryPerm pairing)^[n] d = d :=
    fkRectBlackBoundaryPerm_pow_length_apply pairing d
  have horig : (fkMedialBoundaryStep pairing)^[n] d.1 = d.1 := by
    rw [← fkMedialBlackBoundaryPerm_iterate_val pairing d n, hblack]
  have hreturn : (fkMedialBoundaryStep dualPairing)^[n]
      (fkRectMedialDualShiftDart R d.1) =
        fkRectMedialDualShiftDart R d.1 := by
    rw [← fkRectMedialDualShiftDart_boundaryStep_iterate R omega d.1 n,
      horig]
  exact p.copy rfl (congrArg (fkRectMedialDartPrimalLabel R) hreturn)


def FKRectWalkAvoidsRowSeam
    (R : FKRectTorus) {eta : R.Configuration} {x : R.Vertex}
    (p : (fkRectOpenGraph R eta).Walk x x) : Prop :=
  ∀ e ∈ p.edges, ¬ fkRectCrossesVerticalSeam R e


end
end StatMech.FrontierD
