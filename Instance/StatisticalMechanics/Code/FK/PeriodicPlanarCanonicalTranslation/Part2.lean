module
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalFKG
public import Theorem.StatisticalMechanics.Code.FK.FKGeneralQTranslation.Part2
public import Def.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalTranslation.Part2
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

noncomputable instance PeriodicGraph.instDecidableRelShiftedBufferedGraph
    (P : PeriodicGraph V) (z : Site 2) (n : Nat) :
    DecidableRel (P.shiftedBufferedGraph z n).Adj := Classical.decRel _

end StatMech.FK.PeriodicPlanar
