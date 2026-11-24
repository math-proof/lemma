module
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalTranslation.Part4
public import Theorem.StatisticalMechanics.Code.FK.FreeTailTriviality
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalErgodicity
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators ENNReal StatMech symmDiff


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalErgodicity.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace FK

namespace PeriodicPlanar

open Lattice

variable {V : Type*} [Countable V] [DecidableEq V]


abbrev PeriodicGraph.IsBufferedTailEvent (P : PeriodicGraph V)
    (s : Set (ConfigSpace (Sym2 V))) : Prop :=
  AtiTailEvent P.bufferedEdgeWindow s

end PeriodicPlanar
end FK
end StatMech
