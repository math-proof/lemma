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
import Structure.StatisticalMechanics.Code.Universality.HexW1ExitGeom


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


namespace HexStraightSide

variable {inRegion interior : ℂ → Prop} {a : ℂ} {h0 : ℤ} {z : ℂ}
    (S : HexStraightSide inRegion interior a h0 z)


theorem dir_eq (t : ℤ) (ts : List ℤ)
    (hadm : (HexWalk.ofTurns a h0 (t :: ts)).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 (t :: ts)).StaysIn inRegion
      ∧ (HexWalk.ofTurns a h0 (t :: ts)).EndsAt z) :
    HexWalk.halfStep (hexInfra_headAccum h0 (t :: ts)) = HexWalk.halfStep S.H := by
  
  have hmem : z - HexWalk.halfStep (hexInfra_headAccum h0 (t :: ts))
      ∈ (HexWalk.ofTurns a h0 (t :: ts)).vertices :=
    hexW1Exit_penult_eq_of_endsAt a h0 z t ts hadm.2.2
  
  have hne : z - HexWalk.halfStep (hexInfra_headAccum h0 (t :: ts))
      ≠ z + HexWalk.halfStep (hexInfra_headAccum h0 (t :: ts)) :=
    hexW1Exit_penult_ne_last z (hexInfra_headAccum h0 (t :: ts))
  
  have hpen : interior (z - HexWalk.halfStep (hexInfra_headAccum h0 (t :: ts))) :=
    S.interiorVertices (t :: ts) hadm _ hmem hne
  
  have heq : z - HexWalk.halfStep (hexInfra_headAccum h0 (t :: ts))
      = z + HexWalk.halfStep (hexInfra_headAccum h0 (t :: ts) + 3) := by
    rw [hexW1Exit_halfStep_add_three]; ring
  rw [heq] at hpen
  
  have hu := S.uniqueInterior (hexInfra_headAccum h0 (t :: ts) + 3) hpen
  
  rw [hexW1Exit_halfStep_add_three, hexW1Exit_halfStep_add_three] at hu
  exact neg_injective hu


theorem side_exit (t : ℤ) (ts : List ℤ)
    (hadm : (HexWalk.ofTurns a h0 (t :: ts)).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 (t :: ts)).StaysIn inRegion
      ∧ (HexWalk.ofTurns a h0 (t :: ts)).EndsAt z) :
    hexInfra_midAccum a h0 (t :: ts) + HexWalk.halfStep (hexInfra_headAccum h0 (t :: ts))
      = z + HexWalk.halfStep S.H :=
  hexW1Exit_lastVertex_of_dir a h0 z S.H (t :: ts) hadm.2.2 (S.dir_eq t ts hadm)

end HexStraightSide
end StatMech.Universality
