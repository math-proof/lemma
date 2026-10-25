/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPooledTraceFiber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPooledGateSplit
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedSourceTrace.Part3
import Abbrev.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPooledTraceFiber
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def lpReplicaOffdiagPooledTargetLeftIntermediate
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaDecoratedOrbitAtom G sites
      (lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i)
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) q) :
    LPReplicaDecoratedOrbitAtom G sites
      (lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i) ∅ q := by
  classical
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  have hfixed : (Sj ∆ T).map
      lpReplicaCurrentReflect.toEmbedding = Sj ∆ T := by
    simpa only [Sj, T] using
      lpReplicaCurrentReflect_seam_symmDiff_ghost G sites j
  let d := lpReplicaDecoratedOrbitAtomFixedRowGateData
    G sites Si (Sj ∆ T) q hfixed y
  let m := y.1.1.1
  let e := endsM (lpReplicaCurrentGraph G sites) m
  let K := lpReplicaRowCopies G sites m d.1 true
  let P := edgeComponent e K
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
  let target := lpReplicaCollisionProfile G sites
    (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
    (profileFlux (lpReplicaCurrentGraph G sites) m P)
  let pooled := lpReplicaPooledSelectedSlotStateOfCopies
    G sites m q y.1.1.2 P y.2.2
  let repaired := lpReplicaPooledSelectedSlotMove G sites q pooled
  let movedTag := lpReplicaPartialReflectTagRaw G sites m P d.1
  have hs := lpReplicaRowGate_pooledTargetSplit
    G sites i j m q y.1.1.2 d.1 y.2.2 d.2
  have hs' : repaired.profile = target ∧
      ((lpReplicaPooledSelectedOrbitLabelEquivSlotState
        G sites q).symm repaired).2.2.1 =
          lpReplicaProfileOrbitLabelPartialReflectCopies
            G sites q m y.1.1.2 P y.2.2 ∧
      LPReplicaRowGate G sites target Si ∅ movedTag := by
    simpa only [e, K, P, target, pooled, repaired, movedTag, Si, Sj, T]
      using hs
  let Lrepaired := ((lpReplicaPooledSelectedOrbitLabelEquivSlotState
    G sites q).symm repaired).2.2.1
  let Ltarget : LPReplicaProfileOrbitLabel G sites q target :=
    cast (congrArg (LPReplicaProfileOrbitLabel G sites q) hs'.1) Lrepaired
  have horbit : lpReplicaSymmetrizedProfile G sites target = q := by
    exact hs'.1 ▸ repaired.orbit
  simpa only [Si] using lpReplicaDecoratedOrbitAtomOfRowGate
    G sites target q movedTag Si ∅ horbit hs'.2.2 Ltarget


noncomputable def lpReplicaOffdiagPooledTargetRightIntermediate
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaDecoratedOrbitAtom G sites
      (lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j)
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) q) :
    LPReplicaDecoratedOrbitAtom G sites
      (lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j) ∅ q :=
  lpReplicaOffdiagPooledTargetLeftIntermediate G sites j i q y


noncomputable def lpReplicaOffdiagPooledTargetIntermediate
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    LPReplicaOffdiagDecoratedTarget G sites i j q ->
      LPReplicaOffdiagPooledIntermediateAtom G sites i j q
  | Sum.inl y => Sum.inl
      (lpReplicaOffdiagPooledTargetLeftIntermediate G sites i j q y)
  | Sum.inr y => Sum.inr
      (lpReplicaOffdiagPooledTargetRightIntermediate G sites i j q y)


noncomputable def lpReplicaOffdiagPooledSourceIntermediate
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    LPReplicaOffdiagPooledIntermediateAtom G sites i j q := by
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
  let m := z.1.1.1
  let e := endsM (lpReplicaCurrentGraph G sites) m
  let K := lpReplicaRowCopies G sites m d.1 true
  let P := edgeComponent e K
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
  let target := lpReplicaCollisionProfile G sites
    (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
    (profileFlux (lpReplicaCurrentGraph G sites) m P)
  let pooled := lpReplicaPooledSelectedSlotStateOfCopies
    G sites m q z.1.1.2 P z.2.2
  let repaired := lpReplicaPooledSelectedSlotMove G sites q pooled
  let movedTag := lpReplicaPartialReflectTagRaw G sites m P d.1
  have hs := lpReplicaRowGate_pooledFirstSplit
    G sites hsite hij m q z.1.1.2 d.1 z.2.2 d.2
  have hs' : repaired.profile = target ∧
      ((lpReplicaPooledSelectedOrbitLabelEquivSlotState
        G sites q).symm repaired).2.2.1 =
          lpReplicaProfileOrbitLabelPartialReflectCopies
            G sites q m z.1.1.2 P z.2.2 ∧
      ((LPReplicaRowGate G sites target ∅ Si movedTag ∧
          B ∆ Si = Sj ∆ T) ∨
        (LPReplicaRowGate G sites target ∅ Sj movedTag ∧
          B ∆ Sj = Si ∆ T)) := by
    simpa only [e, K, P, target, pooled, repaired, movedTag,
      Si, Sj, T, B] using hs
  let Lrepaired := ((lpReplicaPooledSelectedOrbitLabelEquivSlotState
    G sites q).symm repaired).2.2.1
  let Ltarget : LPReplicaProfileOrbitLabel G sites q target :=
    cast (congrArg (LPReplicaProfileOrbitLabel G sites q) hs'.1) Lrepaired
  have horbit : lpReplicaSymmetrizedProfile G sites target = q := by
    exact hs'.1 ▸ repaired.orbit
  by_cases hi : LPReplicaRowGate G sites target ∅ Si movedTag
  · have hswap := lpReplicaRowGate_swapRows
      G sites target ∅ Si movedTag hi
    exact Sum.inl (by
      simpa only [Si] using lpReplicaDecoratedOrbitAtomOfRowGate
        G sites target q (lpReplicaSwapRowsTag movedTag)
          Si ∅ horbit hswap Ltarget)
  · have hj : LPReplicaRowGate G sites target ∅ Sj movedTag := by
      rcases hs'.2.2 with hsLeft | hsRight
      · exact False.elim (hi hsLeft.1)
      · exact hsRight.1
    have hswap := lpReplicaRowGate_swapRows
      G sites target ∅ Sj movedTag hj
    exact Sum.inr (by
      simpa only [Sj] using lpReplicaDecoratedOrbitAtomOfRowGate
        G sites target q (lpReplicaSwapRowsTag movedTag)
          Sj ∅ horbit hswap Ltarget)


noncomputable def lpReplicaOffdiagPooledSourceIntermediateFiber
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (u : LPReplicaOffdiagPooledIntermediateAtom G sites i j q) :
    Finset (LPReplicaOffdiagDecoratedSource G sites i j q) := by
  classical
  exact Finset.univ.filter fun z =>
    lpReplicaOffdiagPooledSourceIntermediate
      G sites hsite hij q z = u


noncomputable def lpReplicaOffdiagPooledTargetIntermediateFiber
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (u : LPReplicaOffdiagPooledIntermediateAtom G sites i j q) :
    Finset (LPReplicaOffdiagDecoratedTarget G sites i j q) := by
  classical
  exact Finset.univ.filter fun y =>
    lpReplicaOffdiagPooledTargetIntermediate G sites i j q y = u

end
end StatMech.Ising
