/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/BoxCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.Strip.Part2
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Universality.Defs.Part7
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Def.StatisticalMechanics.Code.RSW.BoxCrossing
open Set MeasureTheory
open scoped ENNReal NNReal


namespace StatMech

namespace RSW

namespace BoxCrossing

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.RSW.Strip

open StatMech.Universality


theorem square_crossing_ge_half (μ : Measure (ConfigSpace (Sym2 (Site 2))))
    [IsProbabilityMeasure μ] (n : ℤ)
    (hdualExists : (squareCrossingEvent n)ᶜ ⊆ squareDualCrossingEvent n)
    (hselfDual : μ.real (squareDualCrossingEvent n) = μ.real (squareCrossingEvent n))
    (hmeas : MeasurableSet (squareCrossingEvent n)) :
    (1 : ℝ) / 2 ≤ μ.real (squareCrossingEvent n) := by
  
  have hcompl : μ.real (squareCrossingEvent n)ᶜ = 1 - μ.real (squareCrossingEvent n) := by
    rw [measureReal_compl hmeas, probReal_univ]
  have hmono : μ.real (squareCrossingEvent n)ᶜ ≤ μ.real (squareDualCrossingEvent n) :=
    measureReal_mono hdualExists
  rw [hselfDual] at hmono
  rw [hcompl] at hmono
  linarith


end BoxCrossing
end RSW
end StatMech
