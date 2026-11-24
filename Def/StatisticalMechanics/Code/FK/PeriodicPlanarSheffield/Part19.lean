module
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoverage.Part3
public import Theorem.StatisticalMechanics.Code.FK.ContinuousRectangleCrossing.Part9
public import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffield.Part18
open Filter MeasureTheory Set SimpleGraph Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


def PeriodicGraph.HasUniqueInfiniteCluster
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V)) : Prop :=
  P.HasInfiniteCluster omega ∧
    ∀ x y, (P.cluster omega x).Infinite →
      (P.cluster omega y).Infinite →
        (P.openSubgraph omega).Reachable x y


def PeriodicGraph.orbitBoxHitsInfinite
    (P : PeriodicGraph V) (n : ℕ) :
    Set (ConfigSpace (Sym2 V)) :=
  {omega | ∃ x ∈ P.orbitBox n, (P.cluster omega x).Infinite}


def PeriodicGraph.translatedOrbitBoxHitsInfinite
    (P : PeriodicGraph V) (z : Site 2) (n : ℕ) :
    Set (ConfigSpace (Sym2 V)) :=
  {omega | ∃ x ∈ P.orbitBox n,
    (P.cluster omega (P.shift z x)).Infinite}

end StatMech.FK.PeriodicPlanar
