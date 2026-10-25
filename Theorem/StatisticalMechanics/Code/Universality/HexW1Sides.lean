/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1Sides.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
import Theorem.StatisticalMechanics.Code.Universality.HexInfraHeading
import Theorem.StatisticalMechanics.Code.Universality.HexConnClosed


namespace StatMech.Universality

open HexWalk List Complex Filter Topology

open scoped BigOperators Real Topology


theorem hexW1_heading_sub_dvd_six_of_sideExit (a : ℂ) (h0 : ℤ) (z : ℂ) (H : ℤ)
    (ts₁ ts₂ : List ℤ)
    (hz₁ : (HexWalk.ofTurns a h0 ts₁).EndsAt z)
    (hv₁ : hexInfra_midAccum a h0 ts₁ + HexWalk.halfStep (hexInfra_headAccum h0 ts₁)
            = z + HexWalk.halfStep H)
    (hz₂ : (HexWalk.ofTurns a h0 ts₂).EndsAt z)
    (hv₂ : hexInfra_midAccum a h0 ts₂ + HexWalk.halfStep (hexInfra_headAccum h0 ts₂)
            = z + HexWalk.halfStep H) :
    (6 : ℤ) ∣ (hexInfra_headAccum h0 ts₁ - hexInfra_headAccum h0 ts₂) := by
  have h1 := hexInfra_finalHeading_mod_of_lastVertex a h0 z H ts₁ hz₁ hv₁
  have h2 := hexInfra_finalHeading_mod_of_lastVertex a h0 z H ts₂ hz₂ hv₂
  omega


end StatMech.Universality
