/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STT.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Abbrev.StatisticalMechanics.Code.Universality.STT
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

def localWeight (p0 p1 p2 : ℝ) (ω : LocalConfig) : ℝ :=
  edgeWeight p0 ω.1 * edgeWeight p1 ω.2.1 * edgeWeight p2 ω.2.2


end Universality
end StatMech
