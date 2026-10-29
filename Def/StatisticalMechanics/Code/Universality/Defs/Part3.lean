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
import Theorem.StatisticalMechanics.Code.Universality.Defs.Part3
open MeasureTheory Set
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice StatMech.TwoDim


variable {d : ℕ}


noncomputable def percolationProbability (d : ℕ) (p : NNReal) (hp : p ≤ 1) : ENNReal :=
  bernoulliProductMeasure (E := Sym2 (Site d)) p hp (percolationEvent d)


def subcriticalDensities (d : ℕ) : Set ℝ :=
  {p : ℝ | ∃ (hp0 : 0 ≤ p) (hp1 : p ≤ 1),
      percolationProbability d ⟨p, hp0⟩ (by exact_mod_cast hp1) = 0}


noncomputable def criticalProbability (d : ℕ) : ℝ :=
  sSup (subcriticalDensities d)


def PositivelyAssociated {E : Type*} (μ : Measure (ConfigSpace E)) : Prop :=
  ∀ A B : Set (ConfigSpace E), IsIncreasing A → IsIncreasing B →
    μ.real A * μ.real B ≤ μ.real (A ∩ B)


end Universality
end StatMech
