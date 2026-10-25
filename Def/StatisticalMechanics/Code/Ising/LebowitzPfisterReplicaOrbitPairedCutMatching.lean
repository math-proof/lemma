/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.Hall.Basic
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitSequentialExchange.Part5
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPairedCutMatching
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def lpReplicaDecoratedOrbitAtomOfCoupledPairedCutCast
    (G : SimpleGraph V) (sites : I -> V)
    (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B A Dtarget : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (horbit : lpReplicaSymmetrizedProfile G sites m = q)
    (hgate : LPReplicaRowGate G sites m B ∅ tag)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (cut : LPReplicaCoupledPairedCut G sites m B tag)
    (hA : B ∆ (cut.half ∆
      cut.half.map lpReplicaCurrentReflect.toEmbedding) = A)
    (hD : cut.half ∆
      cut.half.map lpReplicaCurrentReflect.toEmbedding = Dtarget) :
    LPReplicaDecoratedOrbitAtom G sites A Dtarget q := by
  let y := lpReplicaDecoratedOrbitAtomOfCoupledPairedCut
    G sites m q B tag horbit hgate L cut
  let D := cut.half ∆ cut.half.map lpReplicaCurrentReflect.toEmbedding
  change LPReplicaDecoratedOrbitAtom G sites
    (B ∆ D) D q at y
  let yA : LPReplicaDecoratedOrbitAtom G sites A D q :=
    cast (congrArg
      (fun X => LPReplicaDecoratedOrbitAtom G sites X D q) hA) y
  exact cast (congrArg
    (fun Z => LPReplicaDecoratedOrbitAtom G sites A Z q) hD) yA


noncomputable def lpReplicaDecoratedOrbitAtomOfRightCoupledPairedCutCast
    (G : SimpleGraph V) (sites : I -> V)
    (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B A Dtarget : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (horbit : lpReplicaSymmetrizedProfile G sites m = q)
    (hB : B.map lpReplicaCurrentReflect.toEmbedding = B)
    (hgate : LPReplicaRowGate G sites m ∅ B tag)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (cut : LPReplicaRightCoupledPairedCut G sites m B tag)
    (hA : cut.half ∆
      cut.half.map lpReplicaCurrentReflect.toEmbedding = A)
    (hD : B ∆ (cut.half ∆
      cut.half.map lpReplicaCurrentReflect.toEmbedding) = Dtarget) :
    LPReplicaDecoratedOrbitAtom G sites A Dtarget q := by
  let y := lpReplicaDecoratedOrbitAtomOfRightCoupledPairedCut
    G sites m q B tag horbit hB hgate L cut
  let D := cut.half ∆ cut.half.map lpReplicaCurrentReflect.toEmbedding
  change LPReplicaDecoratedOrbitAtom G sites D (B ∆ D) q at y
  let yA : LPReplicaDecoratedOrbitAtom G sites A (B ∆ D) q :=
    cast (congrArg
      (fun X => LPReplicaDecoratedOrbitAtom G sites X (B ∆ D) q) hA) y
  exact cast (congrArg
    (fun Z => LPReplicaDecoratedOrbitAtom G sites A Z q) hD) yA


def LPReplicaOffdiagCoupledPairedOutput
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q) : Prop :=
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  let B := Si ∆ Sj ∆ T
  (∃ (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
      (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
      (horbit : lpReplicaSymmetrizedProfile G sites m = q)
      (hgate : LPReplicaRowGate G sites m B ∅ tag)
      (L : LPReplicaProfileOrbitLabel G sites q m)
      (cut : LPReplicaCoupledPairedCut G sites m B tag)
      (hD : cut.half ∆
        cut.half.map lpReplicaCurrentReflect.toEmbedding = Sj ∆ T)
      (hA : B ∆ (cut.half ∆
        cut.half.map lpReplicaCurrentReflect.toEmbedding) = Si),
      y = Sum.inl
        (lpReplicaDecoratedOrbitAtomOfCoupledPairedCutCast
          G sites m q B Si (Sj ∆ T) tag horbit hgate L cut hA hD)) ∨
    (∃ (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
      (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
      (horbit : lpReplicaSymmetrizedProfile G sites m = q)
      (hgate : LPReplicaRowGate G sites m B ∅ tag)
      (L : LPReplicaProfileOrbitLabel G sites q m)
      (cut : LPReplicaCoupledPairedCut G sites m B tag)
      (hD : cut.half ∆
        cut.half.map lpReplicaCurrentReflect.toEmbedding = Si ∆ T)
      (hA : B ∆ (cut.half ∆
        cut.half.map lpReplicaCurrentReflect.toEmbedding) = Sj),
      y = Sum.inr
        (lpReplicaDecoratedOrbitAtomOfCoupledPairedCutCast
          G sites m q B Sj (Si ∆ T) tag horbit hgate L cut hA hD))


def lpReplicaOffdiagDecoratedTargetOrbitLabel
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q) ->
      LPReplicaProfileOrbitLabel G sites q
        (lpReplicaOffdiagDecoratedTargetProfile G sites i j q y)
  | Sum.inl y => y.2.2
  | Sum.inr y => y.2.2


def LPReplicaOffdiagCoupledPairedMatch
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q) : Prop :=
  LPReplicaOffdiagCoupledPairedOutput G sites i j q y ∧
    LPReplicaProfileOrbitLabelReallocates G sites q z.2.2
      (lpReplicaOffdiagDecoratedTargetOrbitLabel G sites i j q y)


end
end StatMech.Ising
