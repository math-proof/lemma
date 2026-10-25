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
import Theorem.StatisticalMechanics.Code.FrontierA.IsingInfraredContinuumGreen
open MeasureTheory Set
open scoped BigOperators ComplexConjugate ENNReal Real RealInnerProductSpace


namespace StatMech.FrontierA

noncomputable def isingContinuumGreen (d : Nat) :
    IsingMomentumSpace d → Complex :=
  fun x ↦ ∫ p, Real.fourierChar (-⟪p, x⟫) •
    isingContinuumGreenDensity d p

end StatMech.FrontierA
