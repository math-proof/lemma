/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicCrossingGeometry
import Def.StatisticalMechanics.Code.FK.TriHexPairOrbitCharts.Part8
open SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


theorem hexagonalPairNormal_symm (u v : HexVertex) :
    hexagonalPairNormal u v = hexagonalPairNormal v u := by
  by_cases h : siteLexPositive (v.1 - u.1)
  · have hn : ¬ siteLexPositive (u.1 - v.1) := by
      have := not_siteLexPositive_neg_of_pos h
      simpa only [neg_sub] using this
    simp [hexagonalPairNormal, h, hn]
  · by_cases hr : siteLexPositive (u.1 - v.1)
    · simp [hexagonalPairNormal, h, hr]
    · have hz : v.1 - u.1 = 0 := by
        apply site_eq_zero_of_not_lexPositive_or_neg h
        simpa only [neg_sub] using hr
      have hvu : v.1 = u.1 := sub_eq_zero.mp hz
      have huv : u.1 = v.1 := hvu.symm
      rcases u with ⟨x, b⟩
      rcases v with ⟨y, c⟩
      simp only at huv
      subst y
      cases b <;> cases c <;>
        simp [hexagonalPairNormal, siteLexPositive, boolOrdered]


end StatMech.FK.PeriodicPlanar
