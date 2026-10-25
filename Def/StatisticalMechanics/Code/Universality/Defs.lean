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
import Theorem.StatisticalMechanics.Code.Universality.Defs
open MeasureTheory Set
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice StatMech.TwoDim


variable {d : ℕ}


def originCluster (d : ℕ) (ω : ConfigSpace (Sym2 (Site d))) : Set (Site d) :=
  cluster d ω (0 : Site d)

end Universality
end StatMech
