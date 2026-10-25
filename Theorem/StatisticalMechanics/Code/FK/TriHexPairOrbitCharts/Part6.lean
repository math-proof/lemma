/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicCrossingGeometry
import Instance.StatisticalMechanics.Code.FK.TriHexPairOrbitCharts.Part2
open SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


theorem not_siteLexPositive_neg_of_pos {d : Site 2}
    (h : siteLexPositive d) : ¬ siteLexPositive (-d) := by
  unfold siteLexPositive at h ⊢
  simp only [Pi.neg_apply]
  omega

theorem site_eq_zero_of_not_lexPositive_or_neg {d : Site 2}
    (h : ¬ siteLexPositive d) (hn : ¬ siteLexPositive (-d)) :
    d = 0 := by
  unfold siteLexPositive at h hn
  simp only [Pi.neg_apply] at hn
  have h0 : d 0 = 0 := by omega
  have h1 : d 1 = 0 := by omega
  funext k
  fin_cases k <;> simp [h0, h1]


end StatMech.FK.PeriodicPlanar
