/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitSequentialExchange.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedSourceTrace.Part3
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitExactTagSlotMove
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitSequentialExchange.Part5
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

set_option maxHeartbeats 800000 in


noncomputable def lpReplicaDecoratedOrbitAtomOfCoupledPairedCut
    (G : SimpleGraph V) (sites : I -> V)
    (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (horbit : lpReplicaSymmetrizedProfile G sites m = q)
    (hgate : LPReplicaRowGate G sites m B ∅ tag)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (cut : LPReplicaCoupledPairedCut G sites m B tag) :
    let D := cut.half ∆
      cut.half.map lpReplicaCurrentReflect.toEmbedding
    LPReplicaDecoratedOrbitAtom G sites (B ∆ D) D q := by
  dsimp only
  let rawTarget := lpReplicaCollisionProfile G sites
    (profileFlux (lpReplicaCurrentGraph G sites) m
      (Finset.univ \ cut.selector))
    (profileFlux (lpReplicaCurrentGraph G sites) m cut.selector)
  let target := lpReplicaPartialReflectProfile G sites m
    (profileFlux (lpReplicaCurrentGraph G sites) m cut.selector)
  let rawTag := lpReplicaCoupledReflectToggleTagRaw
    G sites m cut.selector tag
  let movedTag := lpReplicaCanonicalPartialReflectToggleTag
    G sites q m horbit L cut.selector tag
  let D := cut.half ∆
    cut.half.map lpReplicaCurrentReflect.toEmbedding
  have hrawGate : LPReplicaRowGate G sites rawTarget (B ∆ D) D rawTag := by
    simpa only [rawTarget, rawTag, D] using
      lpReplicaRowGate_coupledPairedCut G sites m B tag hgate cut
  let relabel := lpReplicaPartialReflectCanonicalRelabelEquiv
    G sites q m horbit L cut.selector
  have htransport := lpReplicaRowGate_transportTag G sites relabel
    (lpReplicaPartialReflectCanonicalRelabelEquiv_ends
      G sites q m horbit L cut.selector)
    (B ∆ D) D rawTag hrawGate
  have htag : lpReplicaTransportTag G sites relabel rawTag = movedTag := by
    funext d
    let Eraw := lpReplicaPartialReflectCopyEquivRaw
      G sites m cut.selector
    let Ecanon := lpReplicaPartialReflectCanonicalCopyEquiv
      G sites q m horbit L cut.selector
    change lpReplicaToggleRows G sites m cut.selector tag
        (Eraw.symm (Eraw (Ecanon.symm d))) =
      lpReplicaToggleRows G sites m cut.selector tag (Ecanon.symm d)
    rw [Eraw.symm_apply_apply]
  have htargetGate : LPReplicaRowGate G sites target (B ∆ D) D movedTag := by
    rw [<- htag]
    exact htransport
  have htargetOrbit : lpReplicaSymmetrizedProfile G sites target = q := by
    exact (lpReplicaSymmetrizedProfile_partialReflectCopies
      G sites m cut.selector).trans horbit
  let Lpartial := lpReplicaProfileOrbitLabelPartialReflectCopies
    G sites q m horbit cut.selector L
  let y := lpReplicaDecoratedOrbitAtomOfRowGate G sites target q movedTag
    (B ∆ D) D htargetOrbit htargetGate Lpartial
  have hD : D.map lpReplicaCurrentReflect.toEmbedding = D :=
    lpReplica_half_symmDiff_reflect_fixed cut.half
  exact cast (congrArg
    (fun Z => LPReplicaDecoratedOrbitAtom G sites (B ∆ D) Z q) hD) y

set_option maxHeartbeats 800000 in


noncomputable def lpReplicaDecoratedOrbitAtomOfRightCoupledPairedCut
    (G : SimpleGraph V) (sites : I -> V)
    (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (horbit : lpReplicaSymmetrizedProfile G sites m = q)
    (hB : B.map lpReplicaCurrentReflect.toEmbedding = B)
    (hgate : LPReplicaRowGate G sites m ∅ B tag)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (cut : LPReplicaRightCoupledPairedCut G sites m B tag) :
    let D := cut.half ∆
      cut.half.map lpReplicaCurrentReflect.toEmbedding
    LPReplicaDecoratedOrbitAtom G sites D (B ∆ D) q := by
  dsimp only
  let rawTarget := lpReplicaCollisionProfile G sites
    (profileFlux (lpReplicaCurrentGraph G sites) m
      (Finset.univ \ cut.selector))
    (profileFlux (lpReplicaCurrentGraph G sites) m cut.selector)
  let target := lpReplicaPartialReflectProfile G sites m
    (profileFlux (lpReplicaCurrentGraph G sites) m cut.selector)
  let rawTag := lpReplicaCoupledReflectToggleTagRaw
    G sites m cut.selector tag
  let movedTag := lpReplicaCanonicalPartialReflectToggleTag
    G sites q m horbit L cut.selector tag
  let D := cut.half ∆
    cut.half.map lpReplicaCurrentReflect.toEmbedding
  have hrawGate : LPReplicaRowGate G sites rawTarget D (B ∆ D) rawTag := by
    simpa only [rawTarget, rawTag, D] using
      lpReplicaRowGate_rightCoupledPairedCut G sites m B tag hgate cut
  let relabel := lpReplicaPartialReflectCanonicalRelabelEquiv
    G sites q m horbit L cut.selector
  have htransport := lpReplicaRowGate_transportTag G sites relabel
    (lpReplicaPartialReflectCanonicalRelabelEquiv_ends
      G sites q m horbit L cut.selector)
    D (B ∆ D) rawTag hrawGate
  have htag : lpReplicaTransportTag G sites relabel rawTag = movedTag := by
    funext d
    let Eraw := lpReplicaPartialReflectCopyEquivRaw
      G sites m cut.selector
    let Ecanon := lpReplicaPartialReflectCanonicalCopyEquiv
      G sites q m horbit L cut.selector
    change lpReplicaToggleRows G sites m cut.selector tag
        (Eraw.symm (Eraw (Ecanon.symm d))) =
      lpReplicaToggleRows G sites m cut.selector tag (Ecanon.symm d)
    rw [Eraw.symm_apply_apply]
  have htargetGate : LPReplicaRowGate G sites target D (B ∆ D) movedTag := by
    rw [← htag]
    exact htransport
  have htargetOrbit : lpReplicaSymmetrizedProfile G sites target = q := by
    exact (lpReplicaSymmetrizedProfile_partialReflectCopies
      G sites m cut.selector).trans horbit
  let Lpartial := lpReplicaProfileOrbitLabelPartialReflectCopies
    G sites q m horbit cut.selector L
  let y := lpReplicaDecoratedOrbitAtomOfRowGate G sites target q movedTag
    D (B ∆ D) htargetOrbit htargetGate Lpartial
  have hD : D.map lpReplicaCurrentReflect.toEmbedding = D :=
    lpReplica_half_symmDiff_reflect_fixed cut.half
  have hBD : (B ∆ D).map lpReplicaCurrentReflect.toEmbedding = B ∆ D := by
    rw [lpReplica_map_symmDiff, hB, hD]
  exact cast (congrArg
    (fun Z => LPReplicaDecoratedOrbitAtom G sites D Z q) hBD) y

end
end StatMech.Ising
