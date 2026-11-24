module
public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
public import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
public import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
public import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
public import Theorem.StatisticalMechanics.Code.TwoDim.Crossings.Part4
public import Def.StatisticalMechanics.Code.Universality.Defs.Part6
open MeasureTheory Set
open scoped ENNReal NNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/Defs.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Universality

open StatMech.Lattice StatMech.TwoDim


variable {d : ℕ}


theorem boxCrossingProperty_iff (μ : Measure (ConfigSpace (Sym2 (Site 2)))) (ρ : ℝ) :
    BoxCrossingProperty μ ρ ↔
      1 < ρ ∧ ∃ n0 : ℕ, 0 < sInf (boxCrossingProbabilities μ ρ n0) :=
  Iff.rfl

end Universality
end StatMech
