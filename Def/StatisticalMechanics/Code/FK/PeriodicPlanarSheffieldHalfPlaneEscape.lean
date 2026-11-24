module
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlane.Part4
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneEscape
open Filter MeasureTheory Set SimpleGraph Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneEscape.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


def PeriodicGraph.setHitsInfinite
    (P : PeriodicGraph V) (S : Set V) :
    Set (ConfigSpace (Sym2 V)) :=
  {omega | ∃ x ∈ S, (P.cluster omega x).Infinite}

end StatMech.FK.PeriodicPlanar
