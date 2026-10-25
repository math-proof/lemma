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
import Abbrev.StatisticalMechanics.Code.FrontierA.IsingInfraredContinuumGreen
open MeasureTheory Set
open scoped BigOperators ComplexConjugate ENNReal Real RealInnerProductSpace


namespace StatMech.FrontierA

def isingMomentumCube (d : Nat) : Set (IsingMomentumSpace d) :=
  {p | ∀ i, |p i| ≤ Real.pi}

noncomputable def isingContinuumDispersion {d : Nat}
    (p : IsingMomentumSpace d) : Real :=
  ∑ i : Fin d, (2 - 2 * Real.cos (p i))

noncomputable def isingContinuumInverseDispersion {d : Nat}
    (p : IsingMomentumSpace d) : Real :=
  if p = 0 then 0 else (isingContinuumDispersion p)⁻¹

noncomputable def isingContinuumGreenDensity (d : Nat) :
    IsingMomentumSpace d → Complex :=
  (isingMomentumCube d).indicator
    (fun p => (isingContinuumInverseDispersion p : Complex))

end StatMech.FrontierA
