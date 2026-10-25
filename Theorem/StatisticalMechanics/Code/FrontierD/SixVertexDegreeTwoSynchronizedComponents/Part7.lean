/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoBranchClosedPhysicalKey.Part6
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part6


namespace StatMech.FrontierD

open SimpleGraph

noncomputable section

set_option maxHeartbeats 800000

theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.transitionAt_endpoints
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (i : Fin seed.walk.length) :
    (seed.walk.getVert i =
        sixVertexDegreeTwoBranchPredecessor homega heta hdegree false
        (seed.transitionAt i) /\
      seed.walk.getVert (i + 1) =
        sixVertexDegreeTwoBranchPredecessor homega heta hdegree true
        (seed.transitionAt i)) \/
    (seed.walk.getVert (i + 1) =
        sixVertexDegreeTwoBranchPredecessor homega heta hdegree false
        (seed.transitionAt i) /\
      seed.walk.getVert i =
        sixVertexDegreeTwoBranchPredecessor homega heta hdegree true
        (seed.transitionAt i)) := by
  exact sixVertexDegreeTwoSynchronizedEdgeTransition_endpoints homega heta
    hdegree ⟨(seed.walk.getVert i, seed.walk.getVert (i + 1)),
      seed.walk.adj_getVert_succ i.isLt⟩


theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.transitionAt_getVert_endpoints
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (i : Fin seed.walk.length) :
    (seed.walk.getVert i =
        sixVertexDegreeTwoBranchPredecessor homega heta hdegree false
          (seed.transitionAt i) /\
      seed.walk.getVert (i + 1) =
        sixVertexDegreeTwoBranchPredecessor homega heta hdegree true
          (seed.transitionAt i)) \/
    (seed.walk.getVert (i + 1) =
        sixVertexDegreeTwoBranchPredecessor homega heta hdegree false
          (seed.transitionAt i) /\
      seed.walk.getVert i =
        sixVertexDegreeTwoBranchPredecessor homega heta hdegree true
          (seed.transitionAt i)) := by
  exact seed.transitionAt_endpoints i


theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.transitionAt_injective
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) :
    Function.Injective seed.transitionAt := by
  intro i j hij
  have hi := seed.transitionAt_getVert_endpoints i
  have hj := seed.transitionAt_getVert_endpoints j
  rw [hij] at hi
  have hget {a b : Nat} (ha : a ≤ seed.walk.length)
      (hb : b ≤ seed.walk.length)
      (h : seed.walk.getVert a = seed.walk.getVert b) : a = b :=
    seed.walk_isPath.getVert_injOn ha hb h
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · apply Fin.ext
    exact hget i.isLt.le j.isLt.le (hi.1.trans hj.1.symm)
  · have hfirst : i.val = j.val + 1 :=
      hget i.isLt.le (Nat.succ_le_of_lt j.isLt) (hi.1.trans hj.1.symm)
    have hsecond : i.val + 1 = j.val :=
      hget (Nat.succ_le_of_lt i.isLt) j.isLt.le (hi.2.trans hj.2.symm)
    omega
  · have hfirst : i.val + 1 = j.val :=
      hget (Nat.succ_le_of_lt i.isLt) j.isLt.le (hi.1.trans hj.1.symm)
    have hsecond : i.val = j.val + 1 :=
      hget i.isLt.le (Nat.succ_le_of_lt j.isLt) (hi.2.trans hj.2.symm)
    omega
  · apply Fin.ext
    exact hget i.isLt.le j.isLt.le (hi.2.trans hj.2.symm)


end
end StatMech.FrontierD
