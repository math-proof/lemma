/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BernoulliGlobalFKG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.Ergodicity
import Theorem.StatisticalMechanics.Code.Probability.InfiniteHarris.Part3
import Theorem.StatisticalMechanics.Code.Universality.BXPAspectTransfer
import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part101
import Theorem.StatisticalMechanics.Code.Universality.BernoulliGlobalFKG
open MeasureTheory Set Filter
open scoped ENNReal NNReal symmDiff


namespace StatMech

namespace Universality

open StatMech.Lattice

open StatMech.Percolation

open StatMech.RSW.Box

open StatMech.RSW.Strip


def MeasurablyPositivelyAssociated {E : Type*}
    (μ : Measure (ConfigSpace E)) : Prop :=
  ∀ A B : Set (ConfigSpace E), MeasurableSet A → MeasurableSet B →
    IsIncreasing A → IsIncreasing B →
      μ.real A * μ.real B ≤ μ.real (A ∩ B)


def HasIncreasingCylinderApproximation {E : Type*}
    (μ : Measure (ConfigSpace E)) (A : Set (ConfigSpace E)) : Prop :=
  ∃ C : ℕ → Set (ConfigSpace E),
    (∀ n, MeasurableSet (C n)) ∧
    (∀ n, IsIncreasing (C n)) ∧
    (∀ n, ∃ F : Finset E,
      _root_.DependsOn ((C n).indicator (fun _ => (1 : ℝ))) (F : Set E)) ∧
    Tendsto (fun n => μ.real (C n ∆ A)) atTop (nhds 0)


end Universality
end StatMech
