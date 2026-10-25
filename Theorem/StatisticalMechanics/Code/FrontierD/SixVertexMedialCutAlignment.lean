/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMedialCutAlignment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialToggleMerge.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexMedialCutAlignment
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkMedialCutSplits_iff_blackDartSwap_sameCycle
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (d : FKMedialBlackDart T) :
    FKMedialCutSplits pairing d.1.1 <->
      (fkMedialBlackBoundaryPerm pairing).SameCycle d
        (fkMedialBlackDartSwap d.1.1 d) := by
  obtain ⟨v, hd | hd⟩ : exists v : T.Vertex,
      d = fkMedialBlackDart0 v \/ d = fkMedialBlackDart1 v :=
    ⟨d.1.1, fkMedialBlackDart_eq_zero_or_one d⟩
  · subst d
    have hbase :
        (fkMedialBlackBoundaryPerm pairing).SameCycle
            (fkMedialBlackDart0 v) (fkMedialBlackDart1 v) <->
          FKMedialCutSplits pairing v :=
      (fkMedial_blackBoundary_sameCycle_iff_reachable pairing _ _).trans
        (fkMedialBlackDarts_reachable_iff_west_east pairing v)
    change FKMedialCutSplits pairing v <->
      (fkMedialBlackBoundaryPerm pairing).SameCycle
        (fkMedialBlackDart0 v) (fkMedialBlackDartSwap v
          (fkMedialBlackDart0 v))
    simpa [fkMedialBlackDartSwap, fkMedialBlackDart0_ne_dart1]
      using hbase.symm
  · subst d
    have hbase :
        (fkMedialBlackBoundaryPerm pairing).SameCycle
            (fkMedialBlackDart0 v) (fkMedialBlackDart1 v) <->
          FKMedialCutSplits pairing v :=
      (fkMedial_blackBoundary_sameCycle_iff_reachable pairing _ _).trans
        (fkMedialBlackDarts_reachable_iff_west_east pairing v)
    change FKMedialCutSplits pairing v <->
      (fkMedialBlackBoundaryPerm pairing).SameCycle
        (fkMedialBlackDart1 v) (fkMedialBlackDartSwap v
          (fkMedialBlackDart1 v))
    rw [Equiv.Perm.sameCycle_comm]
    simpa [fkMedialBlackDartSwap, fkMedialBlackDart0_ne_dart1]
      using hbase.symm


theorem fkMedialCutSplits_toggle_iff_not
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (v : T.Vertex) :
    FKMedialCutSplits (fkMedialTogglePairingAt pairing v) v ↔
      ¬FKMedialCutSplits pairing v := by
  constructor
  · intro hnew hold
    have hforward :=
      fkMedialLoopCount_toggle_of_reachable T pairing v hold
    have hbackward := fkMedialLoopCount_toggle_of_reachable T
      (fkMedialTogglePairingAt pairing v) v hnew
    rw [fkMedialTogglePairingAt_toggle] at hbackward
    omega
  · intro hold
    exact fkMedialLoopGraph_toggle_reachable_of_not_reachable
      pairing v hold


end
end StatMech.FrontierD
