/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoPinchDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.Umlaufsatz.Part4
import Def.StatisticalMechanics.Code.Lattice.NoPinchDual.Part2
open SimpleGraph Function Set


namespace StatMech

namespace Lattice

set_option linter.unnecessarySeqFocus false in


theorem npd_pinch_forces_diagTouch {K : Set (Site 2)} {e₁ e₂ : Dart}
    (he₁ : IsBoundaryDart K e₁) (he₂ : IsBoundaryDart K e₂)
    (hface : dartFace e₁ = dartFace e₂) (hdir : e₁.dir ≠ e₂.dir) :
    npd_DiagTouch K (dartFace e₁) := by
  
  have hf₂ : dartFace e₂ = dartFace e₁ := hface.symm
  unfold npd_DiagTouch
  rcases dartDir_cases e₁ with h1 | h1 | h1 | h1 <;>
    rcases dartDir_cases e₂ with h2 | h2 | h2 | h2 <;>
    
    first
      | exact absurd (h1.trans h2.symm) hdir
      | (first
          | (have c1 := npd_corners_right he₁ h1)
          | (have c1 := npd_corners_up he₁ h1)
          | (have c1 := npd_corners_left he₁ h1)
          | (have c1 := npd_corners_down he₁ h1)) <;>
        (first
          | (have c2 := npd_corners_right he₂ h2)
          | (have c2 := npd_corners_up he₂ h2)
          | (have c2 := npd_corners_left he₂ h2)
          | (have c2 := npd_corners_down he₂ h2)) <;>
        · rw [hf₂] at c2; tauto


theorem npd_noPinch_local_of_noDiagTouch {K : Set (Site 2)} {e₁ e₂ : Dart}
    (he₁ : IsBoundaryDart K e₁) (he₂ : IsBoundaryDart K e₂)
    (hface : dartFace e₁ = dartFace e₂) (hnt : ¬ npd_DiagTouch K (dartFace e₁)) :
    e₁.dir = e₂.dir := by
  by_contra hdir
  exact hnt (npd_pinch_forces_diagTouch he₁ he₂ hface hdir)


theorem npd_dart_eq_of_noDiagTouch {K : Set (Site 2)} {e₁ e₂ : Dart}
    (he₁ : IsBoundaryDart K e₁) (he₂ : IsBoundaryDart K e₂)
    (hface : dartFace e₁ = dartFace e₂) (hnt : ¬ npd_DiagTouch K (dartFace e₁)) :
    e₁ = e₂ :=
  dartFace_eq_of_dir_eq (npd_noPinch_local_of_noDiagTouch he₁ he₂ hface hnt) hface


end Lattice
end StatMech
