/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.jc4_firstreturnK.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc4_tailnotprobed
import Theorem.StatisticalMechanics.Code.Walls.jc5_core.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc7core.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc7loopiscycle
import Theorem.StatisticalMechanics.Code.Walls.jc7loopseparates.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc7ivtnohop
import Theorem.StatisticalMechanics.Code.Walls.jc7getverteqdartface
import Theorem.StatisticalMechanics.Code.Walls.jc8touchingfaceband
import Theorem.StatisticalMechanics.Code.Walls.jc8tworowbands.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc8crossparityleftregion.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc8bdedgelandssupport.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc8cyclenodup
import Theorem.StatisticalMechanics.Code.Walls.jc8subarcwalk
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.OrbitLoopBridge
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
open SimpleGraph Function Set


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem jc8c_touchingFace_ne_descentFace (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (r : Site 2) (j : ℕ)
    (hj : j ≤ (olb_orbitLoop K hK e he).length)
    (htouch : ¬ jc4_FootprintFree K ⟨e, he⟩ r j)
    (u : Site 2) (hu : u 1 ≤ r 1 - 4) :
    u 1 < (olb_orbitLoop K hK e he).getVert j 1 ∧ u ≠ (olb_orbitLoop K hK e he).getVert j := by
  have hlow : r 1 - 3 ≤ (olb_orbitLoop K hK e he).getVert j 1 :=
    jc8tf_touchingFace_lower K hK e he r j hj htouch
  refine ⟨by omega, ?_⟩
  intro heq
  rw [heq] at hu
  omega


theorem jc8c_distinct_touch_descent (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (r : Site 2) (i j : ℕ)
    (hi : i ≤ (olb_orbitLoop K hK e he).length)
    (hti : ¬ jc4_FootprintFree K ⟨e, he⟩ r i)
    (hdesc : (olb_orbitLoop K hK e he).getVert j 1 ≤ r 1 - 4) :
    (olb_orbitLoop K hK e he).getVert i ≠ (olb_orbitLoop K hK e he).getVert j :=
  fun h => (jc8c_touchingFace_ne_descentFace K hK e he r i hi hti
    ((olb_orbitLoop K hK e he).getVert j) hdesc).2 h.symm


end Walls
end StatMech
