/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenRiemann.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingDyadicGreenLowMomentum
import Theorem.StatisticalMechanics.Code.FrontierA.IsingInfraredSpatial
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.MeasureTheory.Order.UpperLower
import Def.StatisticalMechanics.Code.FrontierA.IsingDyadicGreenRiemann.Part5
open Bornology Filter Finset MeasureTheory Set
open scoped BigOperators ComplexConjugate Pointwise Topology


namespace StatMech.FrontierA

variable {d : Nat}

open Lattice

theorem integrable_isingRegularizedCoordinateDensity
    (eta : Real) (heta : 0 < eta) :
    Integrable (isingRegularizedCoordinateDensity eta :
      IsingMomentumCoordinates d → Complex) := by
  have hcontinuous : Continuous
      (fun q : IsingMomentumCoordinates d =>
        (isingRegularizedInverseDispersion eta q : Complex)) :=
    Complex.continuous_ofReal.comp
      (continuous_isingRegularizedInverseDispersion eta heta)
  have hbound : ∀ q : IsingMomentumCoordinates d,
      ‖(isingRegularizedInverseDispersion eta q : Complex)‖ ≤ eta⁻¹ := by
    intro q
    have hmax : 0 < max (isingNormalizedCoordinateDispersion q) eta :=
      lt_of_lt_of_le heta (le_max_right _ _)
    rw [isingRegularizedInverseDispersion, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hmax)]
    exact (inv_le_inv₀ hmax heta).2 (le_max_right _ _)
  have hOn : IntegrableOn
      (fun q : IsingMomentumCoordinates d =>
        (isingRegularizedInverseDispersion eta q : Complex))
      (isingNormalizedCoordinateCube d) := by
    apply IntegrableOn.of_bound
      (isBounded_isingNormalizedCoordinateCube d).measure_lt_top
      hcontinuous.aestronglyMeasurable.restrict eta⁻¹
    exact Filter.Eventually.of_forall hbound
  exact hOn.integrable_indicator
    (measurableSet_isingNormalizedCoordinateCube d)

end StatMech.FrontierA
