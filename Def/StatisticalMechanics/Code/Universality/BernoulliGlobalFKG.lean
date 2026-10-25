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
open MeasureTheory Set Filter
open scoped ENNReal NNReal symmDiff


namespace StatMech

namespace Universality

open StatMech.Lattice

open StatMech.Percolation

open StatMech.RSW.Box

open StatMech.RSW.Strip


def FiniteCylinderPositivelyAssociated {E : Type*}
    (μ : Measure (ConfigSpace E)) : Prop :=
  ∀ (A B : Set (ConfigSpace E)), IsIncreasing A → IsIncreasing B →
    ∀ (F G : Finset E),
      _root_.DependsOn (A.indicator (fun _ => (1 : ℝ))) (F : Set E) →
      _root_.DependsOn (B.indicator (fun _ => (1 : ℝ))) (G : Set E) →
      μ.real A * μ.real B ≤ μ.real (A ∩ B)


end Universality
end StatMech
