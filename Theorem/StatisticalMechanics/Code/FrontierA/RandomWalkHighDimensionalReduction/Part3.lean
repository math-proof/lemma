/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/RandomWalkHighDimensionalReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Theorem.StatisticalMechanics.Code.Sharpness.IsingSharpness
import Def.StatisticalMechanics.Code.FrontierA.RandomWalkHighDimensionalReduction.Part3
open Filter Finset Topology


namespace StatMech.FrontierA

theorem effectiveRandomWalk_bound_transfer {X : Type*}
    (d : ℕ) (epsilon sigma C c xi : ℝ)
    (delta twoPoint green radius : X → ℝ)
    (hdomination : ∀ x, twoPoint x ≤ green x)
    (hgreen : ∀ x, green x ≤ delta x +
      highDimensionalRandomWalkTail d epsilon sigma C c xi (radius x)) :
    ∀ x, twoPoint x ≤ delta x +
      highDimensionalRandomWalkTail d epsilon sigma C c xi (radius x) := by
  intro x
  exact (hdomination x).trans (hgreen x)


theorem renewal_to_highDimensionalRandomWalk_bound {X : Type*}
    (T : PositiveAdditiveOperator X) (d : ℕ)
    (epsilon sigma C c xi : ℝ)
    (delta twoPoint green radius : X → ℝ)
    (hrenewal : ∀ x, twoPoint x ≤ delta x + T twoPoint x)
    (hpartial : ∀ x, Tendsto (fun n => randomWalkPartial T delta n x)
      atTop (nhds (green x)))
    (hremainder : ∀ x, Tendsto (fun n => randomWalkIterate T n twoPoint x)
      atTop (nhds 0))
    (hgreen : ∀ x, green x ≤ delta x +
      highDimensionalRandomWalkTail d epsilon sigma C c xi (radius x)) :
    ∀ x, twoPoint x ≤ delta x +
      highDimensionalRandomWalkTail d epsilon sigma C c xi (radius x) := by
  exact effectiveRandomWalk_bound_transfer d epsilon sigma C c xi
    delta twoPoint green radius
    (renewal_le_effectiveRandomWalk T delta twoPoint green hrenewal hpartial hremainder)
    hgreen

end StatMech.FrontierA
