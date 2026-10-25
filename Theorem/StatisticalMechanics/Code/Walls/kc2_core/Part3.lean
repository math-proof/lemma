/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ExteriorConnected.Part3
import Theorem.StatisticalMechanics.Code.Walls.kc2_supportisface
import Theorem.StatisticalMechanics.Code.Walls.kc2_dartdircases
import Theorem.StatisticalMechanics.Code.Walls.kc2_rightfaceinK
import Theorem.StatisticalMechanics.Code.Walls.kc2_downfaceoutK
import Theorem.StatisticalMechanics.Code.Walls.kc2_leftupfacecell.Part2
import Def.StatisticalMechanics.Code.Walls.kc2_core.Part2
open Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem kc2_supportOddNonRight_iff_three {K : Set (Site 2)}
    {a : {e : Dart // IsBoundaryDart K e}} :
    kc2_SupportOddNonRight K a ↔
      kc2_DownFaceEven K a ∧ kc2_UpFaceInK K a ∧ kc2_LeftFaceInK K a := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · 
      intro e he hd hsupp
      rw [← kc2_down_residue_is_evenRay (a := a) he hd]
      intro hodd
      exact h (dartFace e) hsupp hodd e he rfl (Or.inl hd)
    · 
      intro e he hd hsupp hodd
      exact h (dartFace e) hsupp hodd e he rfl (Or.inr (Or.inl hd))
    · 
      intro e he hd hsupp hodd
      exact h (dartFace e) hsupp hodd e he rfl (Or.inr (Or.inr hd))
  · rintro ⟨hdown, hup, hleft⟩ z hz hodd e he hzf hdir
    subst hzf
    rcases hdir with hd | hd | hd
    · 
      exact absurd (hdown e he hd hz) hodd
    · exact hup e he hd hz hodd
    · exact hleft e he hd hz hodd


theorem kc2_supportOddInK_of_three {K : Set (Site 2)} {a : {e : Dart // IsBoundaryDart K e}}
    (hdown : kc2_DownFaceEven K a) (hup : kc2_UpFaceInK K a) (hleft : kc2_LeftFaceInK K a) :
    exc_SupportOddInK K a :=
  kc2_supportOddInK_of_nonRight (kc2_supportOddNonRight_iff_three.mpr ⟨hdown, hup, hleft⟩)


theorem kc2_unitCell_core : exc_SupportOddInK unitCell ucBase :=
  exc_unitCell_supportOddInK


theorem kc2_unitCell_supportOddNonRight : kc2_SupportOddNonRight unitCell ucBase :=
  kc2_supportOddNonRight_of_core exc_unitCell_supportOddInK


theorem kc2_unitCell_three :
    kc2_DownFaceEven unitCell ucBase ∧ kc2_UpFaceInK unitCell ucBase ∧
      kc2_LeftFaceInK unitCell ucBase :=
  kc2_supportOddNonRight_iff_three.mp kc2_unitCell_supportOddNonRight


theorem kc2_core_iff_three {K : Set (Site 2)} {a : {e : Dart // IsBoundaryDart K e}} :
    exc_SupportOddInK K a ↔
      (kc2_DownFaceEven K a ∧ kc2_UpFaceInK K a ∧ kc2_LeftFaceInK K a) :=
  kc2_supportOddInK_iff_nonRight.trans kc2_supportOddNonRight_iff_three

end Walls
end StatMech
