/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialToggleMerge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialToggleExact
import Theorem.StatisticalMechanics.Code.FrontierD.PermSameCycleSplit
import Def.StatisticalMechanics.Code.FrontierD.FKMedialToggleMerge
open Equiv SimpleGraph


namespace StatMech.FrontierD

open StatMech.FrontierA

noncomputable section

variable {T : EvenTorus}


theorem fkMedial_reachable_blackRepresentative
    (pairing : FKMedialLoopPairing T) (d : FKMedialDart T) :
    (fkMedialLoopGraph T pairing).Reachable d
      (fkMedialBlackRepresentative T d).1 := by
  classical
  unfold fkMedialBlackRepresentative
  split
  · exact SimpleGraph.Reachable.refl _
  · apply SimpleGraph.Adj.reachable
    rw [fkMedialLoopGraph_adj_iff]
    exact Or.inr rfl


theorem fkMedialLoopGraph_toggle_reachable_mono_of_not_reachable
    (pairing : FKMedialLoopPairing T) (v : T.Vertex)
    (hold : ¬ (fkMedialLoopGraph T pairing).Reachable
      (fkMedialWestDart v) (fkMedialEastDart v))
    {d e : FKMedialDart T}
    (hde : (fkMedialLoopGraph T pairing).Reachable d e) :
    (fkMedialLoopGraph T
      (fkMedialTogglePairingAt pairing v)).Reachable d e := by
  let bd := fkMedialBlackRepresentative T d
  let be := fkMedialBlackRepresentative T e
  have hbOld : (fkMedialLoopGraph T pairing).Reachable bd.1 be.1 :=
    (fkMedial_reachable_blackRepresentative pairing d).symm.trans
      (hde.trans (fkMedial_reachable_blackRepresentative pairing e))
  have hcycleOld : (fkMedialBlackBoundaryPerm pairing).SameCycle bd be :=
    (fkMedial_blackBoundary_sameCycle_iff_reachable pairing bd be).2 hbOld
  have hcycleNew :=
    fkMedialBlackBoundaryPerm_toggle_sameCycle_mono_of_not_reachable
      pairing v hold hcycleOld
  have hbNew : (fkMedialLoopGraph T
      (fkMedialTogglePairingAt pairing v)).Reachable bd.1 be.1 :=
    (fkMedial_blackBoundary_sameCycle_iff_reachable
      (fkMedialTogglePairingAt pairing v) bd be).1 hcycleNew
  exact
    (fkMedial_reachable_blackRepresentative
      (fkMedialTogglePairingAt pairing v) d).trans
        (hbNew.trans
          (fkMedial_reachable_blackRepresentative
            (fkMedialTogglePairingAt pairing v) e).symm)

end
end StatMech.FrontierD
