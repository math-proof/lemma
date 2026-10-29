/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/G3PercDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.Harris
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.TwoDim.Crossings.Part4
import Theorem.StatisticalMechanics.Code.Universality.Defs.Part7
import Def.StatisticalMechanics.Code.Universality.G3PercDefs.Part6
open MeasureTheory Set
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice StatMech.TwoDim

variable {d : ℕ}


theorem G3PositivelyAssociated_iff {E : Type*} (μ : Measure (ConfigSpace E)) :
    G3PositivelyAssociated μ ↔ PositivelyAssociated μ := Iff.rfl


theorem G3PositivelyAssociated.symm {E : Type*} {μ : Measure (ConfigSpace E)}
    (h : G3PositivelyAssociated μ) (A B : Set (ConfigSpace E))
    (hA : IsIncreasing A) (hB : IsIncreasing B) :
    μ.real B * μ.real A ≤ μ.real (B ∩ A) :=
  PositivelyAssociated.symm (G3PositivelyAssociated_iff μ |>.mp h) A B hA hB


theorem G3PositivelyAssociated.sq_le_self {E : Type*} {μ : Measure (ConfigSpace E)}
    (h : G3PositivelyAssociated μ) (A : Set (ConfigSpace E)) (hA : IsIncreasing A) :
    μ.real A * μ.real A ≤ μ.real A :=
  PositivelyAssociated.sq_le_self (G3PositivelyAssociated_iff μ |>.mp h) A hA


theorem bernoulli_g3PositivelyAssociated {E : Type*} [Fintype E] [DecidableEq E]
    {p : NNReal} (hp : p ≤ 1) :
    G3PositivelyAssociated (bernoulliProductMeasure (E := E) p hp) :=
  fun _ _ hA hB => harris_inequality hp hA hB


end Universality
end StatMech
