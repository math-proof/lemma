/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FK.PeriodicPlanarGraph.Part18
import Theorem.StatisticalMechanics.Code.FK.BulkDeviationProof.Part2
import Theorem.StatisticalMechanics.Code.FK.InclusionExclusion.Part4
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoherentLimit.Part8
open Finset Set SimpleGraph MeasureTheory Filter Topology


namespace StatMech

namespace FK

namespace PeriodicPlanar

variable {V : Type*} [DecidableEq V]

variable [Countable V]


def PeriodicGraph.bufferedCylinder (P : PeriodicGraph V) (N : ℕ)
    (S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))) :
    Set (ConfigSpace (Sym2 V)) :=
  P.bufferedRestrict N ⁻¹' S

end PeriodicPlanar
end FK
end StatMech
