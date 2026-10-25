/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredContinuumGreen.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusCharacterCoordinates.Part2
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Def.StatisticalMechanics.Code.FrontierA.IsingInfraredContinuumGreen.Part2
open MeasureTheory Set
open scoped BigOperators ComplexConjugate ENNReal Real RealInnerProductSpace


namespace StatMech.FrontierA

theorem isingContinuumGreen_tendsto_zero
    {d : Nat} (hd : 2 < d) :
    Filter.Tendsto (isingContinuumGreen d)
      (Filter.cocompact (IsingMomentumSpace d)) (nhds 0) := by
  have _hIntegrable := integrable_isingContinuumGreenDensity hd
  simpa only [isingContinuumGreen] using
    (tendsto_integral_exp_inner_smul_cocompact
      (isingContinuumGreenDensity d))

end StatMech.FrontierA
