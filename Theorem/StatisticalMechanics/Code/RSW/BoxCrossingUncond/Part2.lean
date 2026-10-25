/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/BoxCrossingUncond.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.FaceRegion.Part3
import Theorem.StatisticalMechanics.Code.Universality.Defs.Part7
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Def.StatisticalMechanics.Code.RSW.BoxCrossingUncond.Part2
open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal


namespace StatMech

namespace RSW

namespace Uncond

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.RSW.Strip

open StatMech.Universality


theorem square_cross_ge_half (μ : Measure (ConfigSpace (Sym2 (Site 2))))
    [IsProbabilityMeasure μ] (n : ℤ)
    (hsep : (squareCross n)ᶜ ⊆ squareDualCross n)
    (hselfDual : μ.real (squareDualCross n) = μ.real (squareCross n))
    (hmeas : MeasurableSet (squareCross n)) :
    (1 : ℝ) / 2 ≤ μ.real (squareCross n) := by
  have hcompl : μ.real (squareCross n)ᶜ = 1 - μ.real (squareCross n) := by
    rw [measureReal_compl hmeas, probReal_univ]
  have hmono : μ.real (squareCross n)ᶜ ≤ μ.real (squareDualCross n) :=
    measureReal_mono hsep
  rw [hselfDual, hcompl] at hmono
  linarith


end Uncond
end RSW
end StatMech
