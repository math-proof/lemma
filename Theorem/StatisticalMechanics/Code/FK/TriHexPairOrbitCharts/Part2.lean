/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicCrossingGeometry
import Def.StatisticalMechanics.Code.FK.TriHexPairOrbitCharts.Part2
open SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


theorem triangularPairNormal_symm (x y : Site 2) :
    triangularPairNormal x y = triangularPairNormal y x := by
  by_cases hxy : x = y
  · subst y
    rfl
  · have hd : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
    by_cases h : siteLexNonnegative (y - x)
    · have hn := not_siteLexNonnegative_neg_of_ne_zero hd h
      have hn' : ¬ siteLexNonnegative (x - y) := by
        simpa only [neg_sub] using hn
      simp only [triangularPairNormal, h, hn', dite_true, dite_false]
    · have hr : siteLexNonnegative (x - y) := by
        have := siteLexNonnegative_neg_of_not h
        simpa only [neg_sub] using this
      simp only [triangularPairNormal, h, hr, dite_true, dite_false]


end StatMech.FK.PeriodicPlanar
