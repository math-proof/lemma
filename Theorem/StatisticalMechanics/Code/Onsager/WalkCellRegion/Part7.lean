/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCellRegion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CellEulerBound.Part4
import Theorem.StatisticalMechanics.Code.Onsager.InsideConnected
import Def.StatisticalMechanics.Code.Onsager.JedBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanClusterBridge.Part8
import Def.StatisticalMechanics.Code.Onsager.WalkCellRegion.Part6


namespace StatMech.Onsager.WalkCellRegion

open Finset SimpleGraph Set

open StatMech.Lattice

open StatMech.Onsager.BaseCase StatMech.Onsager.NoDoubleWind
  StatMech.Onsager.WalkCrossing StatMech.Onsager.JordanParity
  StatMech.Onsager.InsideConnected StatMech.Onsager.JedBridge


section Walk

variable {m : ℕ}

variable (d : Fin (m + 3) → Fin 4)
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hreflexfree : ∀ i : Fin (m + 3), d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1)


@[simp] theorem mem_interiorCells (p : ℤ × ℤ) :
    p ∈ interiorCells d hclosed hsimple hreflexfree ↔
      cellFace p ∈ (innerComponent d hclosed hsimple hreflexfree).supp := by
  rw [interiorCells, Set.Finite.mem_toFinset]
  rfl


theorem mem_interiorCells_iff_rayParity (p : ℤ × ℤ) :
    p ∈ interiorCells d hclosed hsimple hreflexfree ↔ rayParity d p.1 p.2 = 1 := by
  constructor
  · intro hp
    rw [mem_interiorCells] at hp
    have hcomp := (innerComponent d hclosed hsimple hreflexfree).mem_supp_iff (cellFace p) |>.mp hp
    have hreach : (walkRegionGraph d hclosed hsimple).Reachable
        (cellFace p) (lexInteriorFace d hclosed hsimple hreflexfree) := by
      rw [← ConnectedComponent.eq]
      exact hcomp.trans (by rfl)
    have hpar := rayParity_eq_of_reachable d hclosed hsimple hreach
    simpa [lexInteriorFace_parity d hclosed hsimple hreflexfree] using hpar
  · intro hp
    let C := (walkRegionGraph d hclosed hsimple).connectedComponentMk (cellFace p)
    have hCne : C ≠ jfc_whb_outerRegion (walkP d hclosed hsimple) := by
      intro hEq
      have hcomp : (walkRegionGraph d hclosed hsimple).connectedComponentMk (cellFace p) =
          (walkRegionGraph d hclosed hsimple).connectedComponentMk
            (beacon 2 (outerBoxRadius (walkP d hclosed hsimple) + 1)) := hEq
      have hreach : (walkRegionGraph d hclosed hsimple).Reachable (cellFace p)
          (beacon 2 (outerBoxRadius (walkP d hclosed hsimple) + 1)) :=
        ConnectedComponent.eq.mp hcomp
      have hpar := rayParity_eq_of_reachable d hclosed hsimple hreach
      change rayParity d p.1 p.2 = _ at hpar
      rw [hp, outerBeacon_parity d hclosed hsimple] at hpar
      exact one_ne_zero hpar
    have hCfin : C.supp.Finite :=
      (jfc_whb_bounded_iff_ne_outer (walkP d hclosed hsimple) C).2 hCne
    let inner : jcb_BoundedRegion (walkP d hclosed hsimple) :=
      ⟨innerComponent d hclosed hsimple hreflexfree,
        innerComponent_finite d hclosed hsimple hreflexfree⟩
    let current : jcb_BoundedRegion (walkP d hclosed hsimple) := ⟨C, hCfin⟩
    letI : Unique (jcb_BoundedRegion (walkP d hclosed hsimple)) :=
      jcb_uniqueBoundedRegion_of_nullity_one (walkP d hclosed hsimple)
        (walkSubgraph_nullity_one d hclosed hsimple)
    have hEq : current = inner := Subsingleton.elim _ _
    rw [mem_interiorCells]
    apply (innerComponent d hclosed hsimple hreflexfree).mem_supp_iff (cellFace p) |>.mpr
    change C = innerComponent d hclosed hsimple hreflexfree
    exact congrArg Subtype.val hEq

end Walk
end StatMech.Onsager.WalkCellRegion
