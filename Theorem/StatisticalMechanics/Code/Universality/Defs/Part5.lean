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
import Def.StatisticalMechanics.Code.Universality.Defs.Part4
open MeasureTheory Set
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice StatMech.TwoDim


variable {d : ℕ}


@[simp]
theorem translateConfig_apply (v : Site 2) (ω : ConfigSpace (Sym2 (Site 2)))
    (e : Sym2 (Site 2)) : translateConfig v ω e = ω (e.map (· + v)) := rfl


@[simp]
theorem translateConfig_zero (ω : ConfigSpace (Sym2 (Site 2))) :
    translateConfig (0 : Site 2) ω = ω := by
  funext e
  simp only [translateConfig, add_zero]
  rw [Sym2.map_id', id]


end Universality
end StatMech
