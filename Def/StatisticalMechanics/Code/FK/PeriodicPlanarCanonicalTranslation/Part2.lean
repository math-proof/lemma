/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalFKG
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQTranslation.Part2
import Instance.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalTranslation
open Filter MeasureTheory Set SimpleGraph Topology
open scoped BigOperators


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]

noncomputable def PeriodicGraph.shiftedBufferedGraph
    (P : PeriodicGraph V) (z : Site 2) (n : Nat) :
    SimpleGraph (P.ShiftedBufferedVertex z n) :=
  P.graph.comap Subtype.val

end StatMech.FK.PeriodicPlanar
