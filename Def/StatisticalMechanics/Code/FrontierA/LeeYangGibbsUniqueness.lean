/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangGibbsUniqueness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangBoundaryPressure
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangLocalCorrelationReduction.Part4
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityPhaseCollapse
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityVaryingTemperature.Part2
import Theorem.StatisticalMechanics.Code.Ising.GibbsSimplexInfinite.Part3
import Theorem.StatisticalMechanics.Code.Ising.IsingPlusTIFromPlacement.Part11
import Theorem.StatisticalMechanics.Code.Ising.MinusStateDLR
import Theorem.StatisticalMechanics.Code.Ising.Peierls.Part4
import Theorem.StatisticalMechanics.Code.Ising.ZeroBetaDLRUniqueness
import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingPlusBridge
open Filter Finset MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators BoundedContinuousFunction ENNReal


namespace StatMech.FrontierA

open StatMech.ConfigSpace StatMech.FK StatMech.Ising StatMech.Lattice
  StatMech.Sharpness


noncomputable def fvBoxPressure (eta : ConfigSpace (Site d))
    (n : ℕ) (B : Finset (Sym2 (Site d))) (beta h : ℝ) : ℝ :=
  Real.log (fvZ eta n B beta h) / ((boxFinset d n).card : ℝ)


noncomputable def fvBoxAverageSpin (eta : ConfigSpace (Site d))
    (n : ℕ) (B : Finset (Sym2 (Site d))) (beta h : ℝ) : ℝ :=
  (∑ x ∈ boxFinset d n,
      ∫ omega, spin omega x ∂(fvMeasure eta n B beta h)) /
    ((boxFinset d n).card : ℝ)

end StatMech.FrontierA
