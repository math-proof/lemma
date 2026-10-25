/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8tworowbands.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.jc7core.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc7loopiscycle
import Theorem.StatisticalMechanics.Code.Walls.jc7loopseparates.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc7ivtnohop
import Theorem.StatisticalMechanics.Code.Walls.jc7getverteqdartface
import Theorem.StatisticalMechanics.Code.Walls.jc5_core.Part2
import Theorem.StatisticalMechanics.Code.Lattice.OrbitLoopBridge
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Def.StatisticalMechanics.Code.Walls.jc8tworowbands.Part2
open SimpleGraph Function Set


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem jc8_descentFace_below_touchingFace (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (r : Site 2) (i j : ℕ)
    (hlow : jc8_DescentStaysLow K hK e he r i)
    (hband : jc8_TouchingFaceBand K hK e he r j)
    (htouch : ¬ jc4_FootprintFree K ⟨e, he⟩ r j) :
    (olb_orbitLoop K hK e he).getVert i 1 < (olb_orbitLoop K hK e he).getVert j 1 :=
  jc8_band_separation r _ _ hlow (hband htouch)


theorem jc8_descentFace_ne_touchingFace (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (r : Site 2) (i j : ℕ)
    (hlow : jc8_DescentStaysLow K hK e he r i)
    (hband : jc8_TouchingFaceBand K hK e he r j)
    (htouch : ¬ jc4_FootprintFree K ⟨e, he⟩ r j) :
    (olb_orbitLoop K hK e he).getVert i ≠ (olb_orbitLoop K hK e he).getVert j :=
  jc8_band_ne r _ _ hlow (hband htouch)


theorem jc8_twoRowBands (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (r : Site 2) (i j : ℕ)
    (hlow : jc8_DescentStaysLow K hK e he r i)
    (hband : jc8_TouchingFaceBand K hK e he r j)
    (htouch : ¬ jc4_FootprintFree K ⟨e, he⟩ r j) :
    (olb_orbitLoop K hK e he).getVert i ∈ jc8_descentBand r ∧
      (olb_orbitLoop K hK e he).getVert j ∈ jc8_touchingBand r ∧
      (olb_orbitLoop K hK e he).getVert i 1 < (olb_orbitLoop K hK e he).getVert j 1 ∧
      (olb_orbitLoop K hK e he).getVert i ≠ (olb_orbitLoop K hK e he).getVert j := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [jc8_mem_descentBand]; exact hlow
  · rw [jc8_mem_touchingBand]; exact hband htouch
  · exact jc8_descentFace_below_touchingFace K hK e he r i j hlow hband htouch
  · exact jc8_descentFace_ne_touchingFace K hK e he r i j hlow hband htouch


theorem jc8_touchingFaceBand_of_free (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (r : Site 2) (j : ℕ)
    (hfree : jc4_FootprintFree K ⟨e, he⟩ r j) :
    jc8_TouchingFaceBand K hK e he r j := by
  intro htouch
  exact absurd hfree htouch


theorem jc8_descentStaysLow_of_row (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (r : Site 2) (i : ℕ)
    (hrow : (olb_orbitLoop K hK e he).getVert i 1 ≤ r 1 - 2) :
    jc8_DescentStaysLow K hK e he r i := hrow


theorem jc8_separation_nonvacuous :
    ((![0, 0] : Site 2)) 1 < ((![0, 3] : Site 2)) 1 ∧
      ((![0, 0] : Site 2)) ≠ ((![0, 3] : Site 2)) := by
  refine ⟨?_, ?_⟩
  · 
    
    exact jc8_band_separation (![0, 4] : Site 2) (![0, 0] : Site 2) (![0, 3] : Site 2)
      (by norm_num) (by norm_num)
  · exact jc8_band_ne (![0, 4] : Site 2) (![0, 0] : Site 2) (![0, 3] : Site 2)
      (by norm_num) (by norm_num)


@[simp] theorem jc8_shelfRow_eq (r : Site 2) : jc8_shelfRow r = r 1 - 1 := rfl


theorem jc8_shelfRow_separates (r : Site 2) :
    r 1 - 2 < jc8_shelfRow r ∧ jc8_shelfRow r = r 1 - 1 := by
  unfold jc8_shelfRow; omega


end Walls
end StatMech
