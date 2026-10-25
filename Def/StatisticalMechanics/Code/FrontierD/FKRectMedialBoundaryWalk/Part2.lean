/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialBoundaryWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialReachability
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryPermutation.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareCoverIntersection.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialBoundaryWalk.Part2
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectMedialBoundaryPrimalTrace
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) :
    (n : Nat) → (fkRectOpenGraph R omega).Walk
      (fkRectMedialDartPrimalLabel R d)
      (fkRectMedialDartPrimalLabel R
        ((fkMedialBoundaryStep
          (fkRectConfigurationToMedialPairing R omega))^[n] d))
  | 0 => .nil
  | n + 1 => by
      let step := fkRectMedialBoundaryPrimalStepWalk R omega d
      let tail := fkRectMedialBoundaryPrimalTrace R omega
        (fkMedialBoundaryStep
          (fkRectConfigurationToMedialPairing R omega) d) n
      have joined := step.append tail
      simpa only [Function.iterate_succ_apply] using joined


noncomputable def fkRectMedialBoundaryPrimalOrbitWalk
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) :
    (fkRectOpenGraph R omega).Walk
      (fkRectMedialDartPrimalLabel R d)
      (fkRectMedialDartPrimalLabel R d) := by
  let sigma := fkMedialBoundaryStep
    (fkRectConfigurationToMedialPairing R omega)
  let p := fkRectMedialBoundaryPrimalTrace R omega d (orderOf sigma)
  have hsigma : sigma ^ orderOf sigma = 1 := pow_orderOf_eq_one sigma
  have hreturn : sigma^[orderOf sigma] d = d := by
    rw [← Equiv.Perm.coe_pow]
    simpa only [hsigma, Equiv.Perm.one_apply]
  exact p.copy rfl (congrArg (fkRectMedialDartPrimalLabel R) hreturn)

end
end StatMech.FrontierD
