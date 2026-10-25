/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateTIClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.PlusStateTI.Part2
import Theorem.StatisticalMechanics.Code.Ising.GibbsSimplexUncond
import Def.StatisticalMechanics.Code.Ising.PlusStateTIClose.Part5
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology BoundedContinuousFunction
open scoped BigOperators ENNReal StatMech

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}


theorem pstc_cylinderBcfSet_dense (d : ℕ) : Dense (pstc_cylinderBcfSet d) := by
  rw [Metric.dense_iff]
  intro g ε hε
  obtain ⟨f, hf⟩ := ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints
    (pstc_cylinderAlg d) (pstc_cylinderAlg_separatesPoints d) g.toContinuousMap ε hε
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


theorem pstc_decayFun_plus_eq (β h : ℝ) (g : Multiplicative (Site d)) (φ : ℕ → ℕ)
    (f : ConfigSpace (Site d) →ᵇ ℝ) :
    pstc_decayFun (fun n => plusMeasure d (φ n) β h) g f
      = fun n =>
        (∫ x, f x ∂((plusMeasure d (φ n) β h : ProbabilityMeasure _) : Measure _))
          - (∫ x, f (shift g x)
              ∂((plusMeasure d (φ n) β h : ProbabilityMeasure _) : Measure _)) := rfl


theorem pstc_decayFun_minus_eq (β h : ℝ) (g : Multiplicative (Site d)) (φ : ℕ → ℕ)
    (f : ConfigSpace (Site d) →ᵇ ℝ) :
    pstc_decayFun (fun n => minusMeasure d (φ n) β h) g f
      = fun n =>
        (∫ x, f x ∂((minusMeasure d (φ n) β h : ProbabilityMeasure _) : Measure _))
          - (∫ x, f (shift g x)
              ∂((minusMeasure d (φ n) β h : ProbabilityMeasure _) : Measure _)) := rfl


end Ising
end StatMech
