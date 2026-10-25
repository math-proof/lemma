/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitWindingGeometry.Part10
import Def.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonEmbedding.Part5


namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

noncomputable section

theorem fkRectBlackOrbitMedialRibbonIndexedSite_injective
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    Function.Injective
      (fkRectBlackOrbitMedialRibbonIndexedSite R omega d) := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  let l := fkRectBlackOrbitList pairing d
  intro z w h
  have hblock : (l.get z.1, z.2) = (l.get w.1, w.2) := by
    apply fkRectMedialRibbonBlockSite_injective R pairing
    exact h
  have hdart : l.get z.1 = l.get w.1 := congrArg Prod.fst hblock
  have hslot : z.2 = w.2 := congrArg
    (fun x : FKMedialBlackDart R.medialTorus × Fin 8 => x.2) hblock
  have horbit : l.Nodup := by
    exact Equiv.Perm.nodup_toList
      (fkMedialBlackBoundaryPerm pairing) d
  exact Prod.ext (horbit.injective_get hdart) hslot

@[simp] theorem fkRectMedialRibbonBlockDirection_apply
    (pairing : Bool) (side : FKMedialSide) (t : Fin 8) :
    fkRectMedialRibbonBlockDirection pairing side t =
      (fkRectMedialRibbonBlock pairing side).get
        ⟨t.val, by
          simpa only [fkRectMedialRibbonBlock_length] using t.isLt⟩ := by
  rfl

end
end StatMech.FrontierD
