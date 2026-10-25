/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalFKG
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQTranslation.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalTranslation.Part3
open Filter MeasureTheory Set SimpleGraph Topology
open scoped BigOperators


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]

noncomputable def PeriodicGraph.bufferedEdgeLift
    (P : PeriodicGraph V) (N : Nat) (T : Finset (Sym2 V))
    (hT : ∀ e ∈ T, e ∈ Set.range (P.edgeIncl (P.bufferedRadius N))) :
    Finset (Sym2 (P.BufferedVertex N)) :=
  T.attach.image fun e => (hT e.1 e.2).choose

end StatMech.FK.PeriodicPlanar
