/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Defs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.SLE.Defs.Part6
open scoped UpperHalfPlane NNReal
open MeasureTheory ProbabilityTheory Complex Filter Topology


namespace StatMech.SLE

def IsLoewnerSolutionAt (W : ℝ → ℝ) (g : ℝ → ℂ → ℂ) (z : ℂ) (t : ℝ) : Prop :=
  HasDerivAt (fun s => g s z) (loewnerField W t (g t z)) t


def IsLoewnerSolutionOn (W : ℝ → ℝ) (g : ℝ → ℂ → ℂ) (z : ℂ) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, HasDerivWithinAt (fun u => g u z) (loewnerField W t (g t z)) s t


def SatisfiesLoewnerEquation (W : ℝ → ℝ) (g : ℝ → ℂ → ℂ) : Prop :=
  (∀ z, g 0 z = z) ∧ ∀ z, ∀ t ∈ Set.Ici (0 : ℝ), IsLoewnerSolutionAt W g z t


def SatisfiesMaximalLoewnerEquation
    (W : ℝ → ℝ) (D : ℝ → Set ℂ) (g : ℝ → ℂ → ℂ) : Prop :=
  D 0 = upperHalfPlane ∧
    (∀ z ∈ D 0, g 0 z = z) ∧
    (∀ z ∈ D 0, HasDerivWithinAt (fun t => g t z)
      (loewnerField W 0 (g 0 z)) (Set.Ici (0 : ℝ)) 0) ∧
    ∀ t, 0 < t → ∀ z ∈ D t, IsLoewnerSolutionAt W g z t


end StatMech.SLE
