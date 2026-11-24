module
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalFKG
public import Theorem.StatisticalMechanics.Code.FK.FKGeneralQTranslation.Part2
public import Def.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalTranslation
open Filter MeasureTheory Set SimpleGraph Topology
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalTranslation.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]

abbrev PeriodicGraph.ShiftedBufferedVertex
    (P : PeriodicGraph V) (z : Site 2) (n : Nat) :=
  {v : V // v ∈ P.shiftedBufferedVertices z n}

end StatMech.FK.PeriodicPlanar
