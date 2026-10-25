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
import Def.StatisticalMechanics.Code.Onsager.WalkCellRegion.Part4


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


theorem outerBeacon_parity :
    rayParity d
      (beacon 2 (outerBoxRadius (walkP d hclosed hsimple) + 1) 0)
      (beacon 2 (outerBoxRadius (walkP d hclosed hsimple) + 1) 1) = 0 := by
  apply rayParity_topOutside d _ _ (outerBoxRadius (walkP d hclosed hsimple))
  · intro j
    have hj := outerBoxRadius_spec (walkP d hclosed hsimple) j
    rw [mem_box] at hj
    have hj1 := hj 1
    change (pos d j).2.natAbs ≤ outerBoxRadius (walkP d hclosed hsimple) at hj1
    omega
  · change (outerBoxRadius (walkP d hclosed hsimple) : ℤ) ≤
      (outerBoxRadius (walkP d hclosed hsimple) : ℤ) + 1 + 1
    omega


theorem innerComponent_finite :
    (innerComponent d hclosed hsimple hreflexfree).supp.Finite := by
  apply (jfc_whb_bounded_iff_ne_outer (walkP d hclosed hsimple)
    (innerComponent d hclosed hsimple hreflexfree)).2
  intro heq
  have hcomp :
      (walkRegionGraph d hclosed hsimple).connectedComponentMk
          (lexInteriorFace d hclosed hsimple hreflexfree) =
        (walkRegionGraph d hclosed hsimple).connectedComponentMk
          (beacon 2 (outerBoxRadius (walkP d hclosed hsimple) + 1)) := by
    exact heq
  have hreach : (walkRegionGraph d hclosed hsimple).Reachable
      (lexInteriorFace d hclosed hsimple hreflexfree)
      (beacon 2 (outerBoxRadius (walkP d hclosed hsimple) + 1)) :=
    ConnectedComponent.eq.mp hcomp
  have hp := rayParity_eq_of_reachable d hclosed hsimple hreach
  rw [lexInteriorFace_parity d hclosed hsimple hreflexfree,
    outerBeacon_parity d hclosed hsimple] at hp
  exact one_ne_zero hp


end Walk
end StatMech.Onsager.WalkCellRegion
