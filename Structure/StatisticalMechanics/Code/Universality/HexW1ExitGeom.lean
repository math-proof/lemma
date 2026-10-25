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
import Theorem.StatisticalMechanics.Code.Universality.HexW1ExitGeom


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


structure HexStraightSide (inRegion interior : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ) where
  
  H : ℤ
  

  uniqueInterior : ∀ h : ℤ, interior (z + HexWalk.halfStep h)
      → HexWalk.halfStep h = HexWalk.halfStep (H + 3)
  


  interiorVertices : ∀ ts : List ℤ, (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z
      → ∀ v ∈ (HexWalk.ofTurns a h0 ts).vertices,
          v ≠ z + HexWalk.halfStep (hexInfra_headAccum h0 ts) → interior v

end StatMech.Universality
