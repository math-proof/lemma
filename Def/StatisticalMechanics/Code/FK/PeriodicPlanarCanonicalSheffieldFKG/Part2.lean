module
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalFKG
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectanglePreference.Part4
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalSheffieldFKG
open Filter MeasureTheory Set SimpleGraph Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalSheffieldFKG.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FK.PeriodicPlanar

variable {V : Type*} [DecidableEq V] [Countable V]


def PeriodicGraph.finiteWitnessInfiniteEvent
    (P : PeriodicGraph V) (S : Finset V)
    (Q : V -> Set (ConfigSpace (Sym2 V))) :
    Set (ConfigSpace (Sym2 V)) :=
  ⋃ x ∈ (S : Set V), Q x ∩ {omega | (P.cluster omega x).Infinite}


def PeriodicGraph.finiteWitnessBoundaryApprox
    (P : PeriodicGraph V) (S : Finset V)
    (Q : V -> Set (ConfigSpace (Sym2 V))) (n : Nat) :
    Set (ConfigSpace (Sym2 V)) :=
  ⋃ x ∈ (S : Set V), Q x ∩
    P.bufferedCylinder n (P.bufferedSetBoundaryEvent ({x} : Set V) n)

end StatMech.FK.PeriodicPlanar
