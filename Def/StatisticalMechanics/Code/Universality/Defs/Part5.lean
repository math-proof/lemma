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
import Theorem.StatisticalMechanics.Code.Universality.Defs.Part5
open MeasureTheory Set
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice StatMech.TwoDim


variable {d : ℕ}


def translatedHorizontalCrossingEvent (v : Site 2) (a b : ℤ) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  (translateConfig v) ⁻¹' (horizontalCrossingEvent a b)


def translatedVerticalCrossingEvent (v : Site 2) (a b : ℤ) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  (translateConfig v) ⁻¹' (verticalCrossingEvent a b)


end Universality
end StatMech
