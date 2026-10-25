/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPooledTraceFiber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPooledGateSplit
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedSourceTrace.Part3
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPooledTraceFiber
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def lpReplicaOffdiagPooledSourceTraceIndex
    (G : SimpleGraph V) (sites : I -> V)
    (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    LPReplicaOffdiagPooledTraceIndex G sites q := by
  classical
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  let B := Si ∆ Sj ∆ T
  have hfixed : B.map lpReplicaCurrentReflect.toEmbedding = B := by
    simpa only [B, Si, Sj, T] using
      lpReplicaCurrentReflect_offdiagSource G sites i j
  let d := lpReplicaDecoratedOrbitAtomFixedRowGateData
    G sites ∅ B q hfixed z
  let e := endsM (lpReplicaCurrentGraph G sites) z.1.1.1
  let K := lpReplicaRowCopies G sites z.1.1.1 d.1 true
  let P := edgeComponent e K
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
  let target := lpReplicaCollisionProfile G sites
    (profileFlux (lpReplicaCurrentGraph G sites) z.1.1.1
      (Finset.univ \ P))
    (profileFlux (lpReplicaCurrentGraph G sites) z.1.1.1 P)
  let movedTag := lpReplicaPartialReflectTagRaw
    G sites z.1.1.1 P d.1
  let repaired := lpReplicaDecoratedOrbitAtomPooledTraceState
    G sites ∅ B q hfixed z
  if LPReplicaRowGate G sites target ∅ Si movedTag then
    exact Sum.inl repaired
  else
    exact Sum.inr repaired


noncomputable def lpReplicaOffdiagPooledTargetTraceIndex
    (G : SimpleGraph V) (sites : I -> V)
    (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q) :
    LPReplicaOffdiagPooledTraceIndex G sites q := by
  classical
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  cases y with
  | inl y =>
      have hfixed : (Sj ∆ T).map
          lpReplicaCurrentReflect.toEmbedding = Sj ∆ T := by
        simpa only [Sj, T] using
          lpReplicaCurrentReflect_seam_symmDiff_ghost G sites j
      exact Sum.inl (lpReplicaDecoratedOrbitAtomPooledTraceState
        G sites Si (Sj ∆ T) q hfixed y)
  | inr y =>
      have hfixed : (Si ∆ T).map
          lpReplicaCurrentReflect.toEmbedding = Si ∆ T := by
        simpa only [Si, T] using
          lpReplicaCurrentReflect_seam_symmDiff_ghost G sites i
      exact Sum.inr (lpReplicaDecoratedOrbitAtomPooledTraceState
        G sites Sj (Si ∆ T) q hfixed y)


noncomputable def lpReplicaOffdiagPooledSourceTraceFiber
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (u : LPReplicaOffdiagPooledTraceIndex G sites q) :
    Finset (LPReplicaOffdiagDecoratedSource G sites i j q) := by
  classical
  exact Finset.univ.filter fun z =>
    lpReplicaOffdiagPooledSourceTraceIndex G sites i j q z = u


noncomputable def lpReplicaOffdiagPooledTargetTraceFiber
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (u : LPReplicaOffdiagPooledTraceIndex G sites q) :
    Finset (LPReplicaOffdiagDecoratedTarget G sites i j q) := by
  classical
  exact Finset.univ.filter fun y =>
    lpReplicaOffdiagPooledTargetTraceIndex G sites i j q y = u

end
end StatMech.Ising
