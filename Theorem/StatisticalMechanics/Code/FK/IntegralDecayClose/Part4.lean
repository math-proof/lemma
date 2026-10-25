/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IntegralDecayClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.IntegralShiftDecay.Part2
import Theorem.StatisticalMechanics.Code.FK.DensityFiniteToInfinite.Part2
import Theorem.StatisticalMechanics.Code.FK.FKUniquenessClose
import Def.StatisticalMechanics.Code.FK.IntegralDecayClose.Part4
open MeasureTheory Filter Topology BoundedContinuousFunction
open StatMech.ConfigSpace StatMech.Lattice


namespace StatMech

namespace FK

open StatMech.IsingFK

variable {d : ℕ}


theorem idc_cylinderBcfSet_dense (d : ℕ) : Dense (idc_cylinderBcfSet d) := by
  rw [Metric.dense_iff]
  intro g ε hε
  obtain ⟨f, hf⟩ := ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints
    (idc_cylinderAlg d) (idc_cylinderAlg_separatesPoints d) g.toContinuousMap ε hε
  refine ⟨BoundedContinuousFunction.mkOfCompact (f : C(_, ℝ)), ?_, ⟨(f : C(_, ℝ)), f.2, rfl⟩⟩
  rw [Metric.mem_ball]
  have hg : BoundedContinuousFunction.mkOfCompact g.toContinuousMap = g :=
    BoundedContinuousFunction.ext (congrFun rfl)
  calc dist (BoundedContinuousFunction.mkOfCompact (f : C(_, ℝ))) g
      = dist (BoundedContinuousFunction.mkOfCompact (f : C(_, ℝ)))
          (BoundedContinuousFunction.mkOfCompact g.toContinuousMap) := by rw [hg]
    _ = dist (f : C(_, ℝ)) g.toContinuousMap := BoundedContinuousFunction.dist_mkOfCompact _ _
    _ = ‖(f : C(_, ℝ)) - g.toContinuousMap‖ := dist_eq_norm _ _
    _ < ε := hf


end FK
end StatMech
