/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalErgodicity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalTranslation.Part4
import Theorem.StatisticalMechanics.Code.FK.FreeTailTriviality
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalErgodicity
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators ENNReal StatMech symmDiff


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
