/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoBranchClosedPhysicalKey.Part6
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part7


namespace StatMech.FrontierD

open SimpleGraph

noncomputable section

set_option maxHeartbeats 800000

theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.transitionAt_eq_get
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (i : Fin seed.walk.length) :
    seed.transitionAt i =
      seed.transitions.get (Fin.cast seed.transitions_length.symm i) := by
  unfold SixVertexDegreeTwoSynchronizedHighChargeSeed.transitionAt
    SixVertexDegreeTwoSynchronizedHighChargeSeed.transitions
  simp only [List.get_eq_getElem, List.getElem_map]
  congr 1
  exact (seed.walk.darts_getElem_eq_getVert i
    (by simpa [SimpleGraph.Walk.length_darts] using i.isLt)).symm


theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.transitions_nodup
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) :
    seed.transitions.Nodup := by
  rw [List.nodup_iff_injective_get]
  intro i j hij
  let e : Fin seed.transitions.length ≃ Fin seed.walk.length :=
    finCongr seed.transitions_length
  apply e.injective
  apply seed.transitionAt_injective
  rw [seed.transitionAt_eq_get (e i), seed.transitionAt_eq_get (e j)]
  simpa [e] using hij


end
end StatMech.FrontierD
