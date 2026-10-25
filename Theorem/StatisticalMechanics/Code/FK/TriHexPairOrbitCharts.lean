/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicCrossingGeometry
import Instance.StatisticalMechanics.Code.FK.TriHexPairOrbitCharts
open SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


theorem siteLexNonnegative_zero :
    siteLexNonnegative (0 : Site 2) := by
  right
  simp

theorem siteLexNonnegative_neg_of_not
    {d : Site 2} (h : ¬ siteLexNonnegative d) :
    siteLexNonnegative (-d) := by
  unfold siteLexNonnegative at h ⊢
  simp only [Pi.neg_apply]
  by_cases h0 : d 0 = 0
  · right
    constructor
    · simp [h0]
    · have h1 : ¬ 0 <= d 1 := by tauto
      omega
  · left
    have hle : d 0 <= 0 := by omega
    omega

theorem not_siteLexNonnegative_neg_of_ne_zero
    {d : Site 2} (hd : d ≠ 0) (h : siteLexNonnegative d) :
    ¬ siteLexNonnegative (-d) := by
  unfold siteLexNonnegative at h ⊢
  simp only [Pi.neg_apply]
  intro hn
  by_cases h0 : d 0 = 0
  · have h1 : d 1 ≠ 0 := by
      intro h1
      apply hd
      funext k
      fin_cases k <;> simp [h0, h1]
    rcases h with hpos | ⟨_, hnonneg⟩
    · omega
    rcases hn with hneg | ⟨_, hnonpos⟩
    · omega
    · omega
  · rcases h with hpos | ⟨hz, _⟩
    · rcases hn with hneg | ⟨hz', _⟩ <;> omega
    · exact h0 hz


end StatMech.FK.PeriodicPlanar
