/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarGraph.Part4
open Finset Set SimpleGraph
open MeasureTheory


namespace StatMech

namespace FK

namespace PeriodicPlanar

open Lattice


variable {V : Type*} [DecidableEq V]


noncomputable def PeriodicGraph.freeFiniteMeasure (P : PeriodicGraph V) (n : ℕ)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ProbabilityMeasure (ConfigSpace (Sym2 V)) :=
  ⟨((P.freeFinitePMF n hp hp1 hq).toMeasure).map (P.extendEdge n),
    inferInstance⟩


noncomputable def PeriodicGraph.wiredFiniteMeasure (P : PeriodicGraph V) (n : ℕ)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ProbabilityMeasure (ConfigSpace (Sym2 V)) :=
  ⟨((P.wiredFinitePMF n hp hp1 hq).toMeasure).map (P.extendEdge n),
    inferInstance⟩

section Countable

variable [Countable V]


noncomputable def PeriodicGraph.freeInfiniteVolume (P : PeriodicGraph V)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ProbabilityMeasure (ConfigSpace (Sym2 V)) :=
  (prokhorov_seq_compact (fun n => P.freeFiniteMeasure n hp hp1 hq)).choose

end Countable
end PeriodicPlanar
end FK
end StatMech
