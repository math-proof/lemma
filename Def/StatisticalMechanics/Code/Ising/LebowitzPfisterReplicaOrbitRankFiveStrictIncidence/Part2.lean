/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictIncidence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveRouting.Part2
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictIncidence.Part2


namespace StatMech.Ising

noncomputable section

open scoped symmDiff

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

def LPReplicaDecoratedOrbitAtom.HasStrictPhysicalDoubleIncidence
    (G : SimpleGraph V) (sites : I -> V)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaDecoratedOrbitAtom G sites A B q) : Prop :=
  let oz := lpReplicaDecoratedOrbitAtomEquivOrientedFourColor
    G sites A B q z
  let tag := lpReplicaOrientedFourColorTag G sites A B q oz
  let K := lpReplicaRowCopies G sites oz.1.1 tag true
  LPReplicaStrictPhysicalDoubleIncidenceRaw G sites oz.1.1 K


def LPReplicaOffdiagDecoratedTarget.HasStrictPhysicalDoubleIncidence
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q) : Prop :=
  match y with
  | Sum.inl z =>
      LPReplicaDecoratedOrbitAtom.HasStrictPhysicalDoubleIncidence
        G sites
          (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i)
          (lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
            lpMatchingGhostSource
              (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
              lpReplicaCurrentGhost1) q z
  | Sum.inr z =>
      LPReplicaDecoratedOrbitAtom.HasStrictPhysicalDoubleIncidence
        G sites
          (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j)
          (lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
            lpMatchingGhostSource
              (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
              lpReplicaCurrentGhost1) q z


def LPReplicaAggregateDecoratedTarget.HasStrictPhysicalDoubleIncidence
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaAggregateDecoratedTarget G sites q) : Prop :=
  LPReplicaDecoratedOrbitAtom.HasStrictPhysicalDoubleIncidence
    G sites
      (lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) y.2.1)
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) y.2.2.1 ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) q y.2.2.2


end
end StatMech.Ising
