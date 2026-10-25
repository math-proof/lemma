/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/Defs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.TwoDim.Crossings.Part4
import Theorem.StatisticalMechanics.Code.Universality.Defs.Part6
open MeasureTheory Set
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice StatMech.TwoDim


variable {d : ℕ}


noncomputable def boxCrossingProbabilities (μ : Measure (ConfigSpace (Sym2 (Site 2))))
    (ρ : ℝ) (n0 : ℕ) : Set ℝ :=
  {x : ℝ | ∃ (n : ℕ) (τ : Site 2), n0 ≤ n ∧
      (x = μ.real (translatedHorizontalCrossingEvent τ ⌊ρ * (n : ℝ)⌋ (n : ℤ))
        ∨ x = μ.real (translatedVerticalCrossingEvent τ (n : ℤ) ⌊ρ * (n : ℝ)⌋))}


noncomputable def boxCrossingInf (μ : Measure (ConfigSpace (Sym2 (Site 2))))
    (ρ : ℝ) (n0 : ℕ) : ℝ :=
  sInf (boxCrossingProbabilities μ ρ n0)


def BoxCrossingProperty (μ : Measure (ConfigSpace (Sym2 (Site 2)))) (ρ : ℝ) : Prop :=
  1 < ρ ∧ ∃ n0 : ℕ, 0 < boxCrossingInf μ ρ n0


end Universality
end StatMech
