/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKErgodicFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.WeakConvergence
import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
open MeasureTheory Filter Topology
open StatMech.ConfigSpace StatMech.Lattice


namespace StatMech

namespace FK

theorem erg_map_eq_of_translated_converges {E : Type*} [Countable E]
    (μ : ℕ → ProbabilityMeasure (ConfigSpace E)) (ν : ProbabilityMeasure (ConfigSpace E))
    {T : ConfigSpace E → ConfigSpace E} (hT : Continuous T)
    (hconv : WeakConvergesTo μ ν)
    (hshift : WeakConvergesTo (fun n => (μ n).map hT.measurable.aemeasurable) ν) :
    ν.map hT.measurable.aemeasurable = ν :=
  tendsto_nhds_unique
    (ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous μ ν hconv hT) hshift


theorem erg_measure_map_eq_of_translated_converges {E : Type*} [Countable E]
    (μ : ℕ → ProbabilityMeasure (ConfigSpace E)) (ν : ProbabilityMeasure (ConfigSpace E))
    {T : ConfigSpace E → ConfigSpace E} (hT : Continuous T)
    (hconv : WeakConvergesTo μ ν)
    (hshift : WeakConvergesTo (fun n => (μ n).map hT.measurable.aemeasurable) ν) :
    Measure.map T (ν : Measure (ConfigSpace E)) = (ν : Measure (ConfigSpace E)) := by
  have h := erg_map_eq_of_translated_converges μ ν hT hconv hshift
  have h2 : ((ν.map hT.measurable.aemeasurable : ProbabilityMeasure (ConfigSpace E))
      : Measure (ConfigSpace E)) = (ν : Measure (ConfigSpace E)) := by rw [h]
  rwa [ProbabilityMeasure.toMeasure_map] at h2


end FK
end StatMech
