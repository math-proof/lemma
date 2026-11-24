module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Theorem.StatisticalMechanics.Code.Universality.STT.Part2
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STT.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Universality

abbrev LocalConfig : Type := Bool × Bool × Bool


end Universality
end StatMech
