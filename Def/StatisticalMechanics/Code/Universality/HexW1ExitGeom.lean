/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1ExitGeom.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexInfraDisplacement.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
import Theorem.StatisticalMechanics.Code.Universality.HexInfraHeading
import Theorem.StatisticalMechanics.Code.Universality.HexW1Sides.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexW1ExitGeom.Part2


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


noncomputable def hexW1Exit_boundarySide (inRegion interior : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (S : HexStraightSide inRegion interior a h0 z) (w : ℤ) (hHL : w ≤ S.H) (hHU : S.H < w + 6)
    (hwin : ∀ ts : List ℤ, (HexWalk.ofTurns a h0 ts).IsLegalSAW
        ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z
      → w ≤ hexInfra_headAccum h0 ts ∧ hexInfra_headAccum h0 ts < w + 6)
    (htrivial : ([] : List ℤ) ∈ ({ts : List ℤ |
        (HexWalk.ofTurns a h0 ts).IsLegalSAW
        ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z} : Set (List ℤ))
      → hexInfra_midAccum a h0 [] + HexWalk.halfStep (hexInfra_headAccum h0 [])
          = z + HexWalk.halfStep S.H) :
    HexBoundarySide inRegion a h0 z where
  H := S.H
  w := w
  hHL := hHL
  hHU := hHU
  exits := by
    intro ts hadm
    refine ⟨?_, hwin ts hadm⟩
    cases ts with
    | nil => exact htrivial hadm
    | cons t ts => exact S.side_exit t ts hadm


end StatMech.Universality
