/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripInterior.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexInfraDisplacement.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexW1ExitGeom.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexStripInterior.Part2


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


noncomputable def hexStrip_straightSide (dregion : ℂ → ℤ → Prop) (inRegion : ℂ → Prop)
    (a : ℂ) (h0 : ℤ) (z : ℂ) (Hd : ℤ)
    (huniq : ∀ h : ℤ, hexStripInterior dregion (z + HexWalk.halfStep h)
        → HexWalk.halfStep h = HexWalk.halfStep (Hd + 3))
    (hbridge : ∀ ts : List ℤ, (HexWalk.ofTurns a h0 ts).IsLegalSAW
        ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z
      → hexStripStaysInDir dregion a h0 ts) :
    HexStraightSide inRegion (hexStripInterior dregion) a h0 z where
  H := Hd
  uniqueInterior := huniq
  interiorVertices := by
    intro ts hadm v hv hvne
    have hzm : hexInfra_midAccum a h0 ts = z := by
      rw [← hexInfra_endMid_eq_midAccum]; exact hadm.2.2
    refine hexStrip_interiorVertices_core dregion a h0 ts hadm.1 (hbridge ts hadm) v hv ?_
    rw [hzm]; exact hvne


end StatMech.Universality
