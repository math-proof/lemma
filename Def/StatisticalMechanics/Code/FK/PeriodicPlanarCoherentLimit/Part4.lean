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
import Instance.StatisticalMechanics.Code.FK.PeriodicPlanarCoherentLimit.Part2
open Finset Set SimpleGraph MeasureTheory Filter Topology


namespace StatMech

namespace FK

namespace PeriodicPlanar

variable {V : Type*} [DecidableEq V]

noncomputable def PeriodicGraph.bufferedVertexInclLE (P : PeriodicGraph V)
    {n m : ℕ} (hnm : n ≤ m) : P.BufferedVertex n ↪ P.BufferedVertex m where
  toFun v := ⟨v.1, P.orbitBox_mono
    (P.bufferedRadius_strictMono.monotone hnm) v.2⟩
  inj' := by
    intro x y h
    have hval : (x : V) = (y : V) :=
      congrArg (fun z : P.BufferedVertex m => (z : V)) h
    exact Subtype.ext hval

end PeriodicPlanar
end FK
end StatMech
