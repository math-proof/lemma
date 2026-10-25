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
import Abbrev.StatisticalMechanics.Code.FK.PeriodicPlanarCoherentLimit
open Finset Set SimpleGraph MeasureTheory Filter Topology


namespace StatMech

namespace FK

namespace PeriodicPlanar

variable {V : Type*} [DecidableEq V]

noncomputable instance PeriodicGraph.instFintypeBufferedVertex
    (P : PeriodicGraph V) (n : ℕ) : Fintype (P.BufferedVertex n) :=
  P.instFintypeOrbitVertex (P.bufferedRadius n)

instance PeriodicGraph.instDecidableEqBufferedVertex
    (P : PeriodicGraph V) (n : ℕ) : DecidableEq (P.BufferedVertex n) :=
  Subtype.instDecidableEq

end PeriodicPlanar
end FK
end StatMech
