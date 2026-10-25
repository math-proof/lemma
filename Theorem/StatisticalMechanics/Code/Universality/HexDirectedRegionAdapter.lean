/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexDirectedRegionAdapter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripNormalizedBoundary.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryAssign.Part3
import Def.StatisticalMechanics.Code.Universality.HexDirectedRegionAdapter


namespace StatMech.Universality

open Complex HexWalk


theorem hexStripInterior_of_headingPeriodic_edge
    (dregion : ℂ → ℤ → Prop) (hperiodic : HexHeadingPeriodic dregion)
    (m : ℂ) (h : ℤ) (hmh : dregion m h) :
    hexStripInterior dregion (m + halfStep h)
      ∧ hexStripInterior dregion (m + halfStep (h + 3)) := by
  have hmh6 : dregion m (h + 6) := hperiodic m h hmh
  have hpairs : (m, h) ≠ (m, h + 6) := by
    intro hp
    have := congrArg Prod.snd hp
    omega
  constructor
  · refine ⟨m, m, h, h + 6, hmh, hmh6, hpairs, Or.inl rfl, ?_⟩
    left
    rw [hexStrip_halfStep_add6]
  · refine ⟨m, m, h, h + 6, hmh, hmh6, hpairs, Or.inr rfl, ?_⟩
    right
    convert rfl using 1
    rw [show (h + 6 + 3 : ℤ) = (h + 3) + 6 by ring,
      hexStrip_halfStep_add6]


theorem not_hexStrip_uniqueInterior_of_headingPeriodic_start
    (dregion : ℂ → ℤ → Prop) (a : ℂ) (h0 : ℤ)
    (hperiodic : HexHeadingPeriodic dregion) (hstart : dregion a h0) :
    ¬(∀ h : ℤ, hexStripInterior dregion (a + halfStep h) →
        halfStep h = halfStep h0) := by
  intro huniq
  have hinterior : hexStripInterior dregion (a + halfStep (h0 + 3)) :=
    (hexStripInterior_of_headingPeriodic_edge dregion hperiodic a h0 hstart).2
  have heq := huniq (h0 + 3) hinterior
  have hdiv : (6 : ℤ) ∣ (h0 + 3 - h0) :=
    (hexUnit_eq_iff_mod _ _).mp (hexInfra_halfStep_inj heq)
  norm_num at hdiv


end StatMech.Universality
