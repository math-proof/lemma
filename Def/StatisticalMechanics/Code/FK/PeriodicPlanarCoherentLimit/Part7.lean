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
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoherentLimit.Part6
open Finset Set SimpleGraph MeasureTheory Filter Topology


namespace StatMech

namespace FK

namespace PeriodicPlanar

variable {V : Type*} [DecidableEq V]

variable [Countable V]


noncomputable def PeriodicGraph.freeBufferedMeasure (P : PeriodicGraph V) (n : ℕ)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ProbabilityMeasure (ConfigSpace (Sym2 V)) :=
  P.freeFiniteMeasure (P.bufferedRadius n) hp hp1 hq


noncomputable def PeriodicGraph.wiredBufferedPMF (P : PeriodicGraph V) (n : ℕ)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    PMF (ConfigSpace (Sym2 (P.BufferedVertex n))) :=
  wiredFkPMF (P.bufferedGraph n) (P.bufferedBoundary n) hp hp1 hq


noncomputable def PeriodicGraph.wiredBufferedMeasure (P : PeriodicGraph V) (n : ℕ)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ProbabilityMeasure (ConfigSpace (Sym2 V)) :=
  ⟨((P.wiredBufferedPMF n hp hp1 hq).toMeasure).map
      (P.extendEdge (P.bufferedRadius n)),
    inferInstance⟩


noncomputable def PeriodicGraph.bufferedRestrict (P : PeriodicGraph V) (n : ℕ)
    (omega : ConfigSpace (Sym2 V)) :
    ConfigSpace (Sym2 (P.BufferedVertex n)) :=
  fun e => omega (P.edgeIncl (P.bufferedRadius n) e)

end PeriodicPlanar
end FK
end StatMech
