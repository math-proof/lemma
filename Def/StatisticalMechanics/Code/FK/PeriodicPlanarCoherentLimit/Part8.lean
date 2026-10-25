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
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoherentLimit.Part7
open Finset Set SimpleGraph MeasureTheory Filter Topology


namespace StatMech

namespace FK

namespace PeriodicPlanar

variable {V : Type*} [DecidableEq V]

variable [Countable V]


noncomputable def PeriodicGraph.bufferedRestrictLE (P : PeriodicGraph V)
    {n m : ℕ} (hnm : n ≤ m)
    (omega : ConfigSpace (Sym2 (P.BufferedVertex m))) :
    ConfigSpace (Sym2 (P.BufferedVertex n)) :=
  fun e => omega (Sym2.map (P.bufferedVertexInclLE hnm) e)

end PeriodicPlanar
end FK
end StatMech
