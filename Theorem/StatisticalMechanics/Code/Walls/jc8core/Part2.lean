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
import Def.StatisticalMechanics.Code.Walls.jc8core
open SimpleGraph Function Set


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem jc8c_crossCount_ge_one_touch_to_free (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (r : Site 2)
    (hdich : jc8c_SideDichotomy K hK e he r)
    {j₀ j₁ : ℕ} (hj₀ : j₀ ≤ (olb_orbitLoop K hK e he).length)
    (hj₁ : j₁ ≤ (olb_orbitLoop K hK e he).length)
    (htouch : ¬ jc4_FootprintFree K ⟨e, he⟩ r j₀)
    (hfree : jc4_FootprintFree K ⟨e, he⟩ r j₁)
    (w : (hypercubicLattice 2).Walk ((olb_orbitLoop K hK e he).getVert j₀)
      ((olb_orbitLoop K hK e he).getVert j₁)) :
    1 ≤ crossCount (jec_leftRegion (olb_orbitLoop K hK e he)) w :=
  jc8_crossCount_ge_one_of_opposite_leftRegion K hK e he w
    (hdich.1 j₀ hj₀ htouch) (hdich.2 j₁ hj₁ hfree)


theorem jc8c_touchingConvex_window (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (r : Site 2)
    (hdich : jc8c_SideDichotomy K hK e he r)
    (hint : jc8c_InsideInterval K hK e he)
    (i j k : ℕ)
    (hi : i ≤ (olb_orbitLoop K hK e he).length)
    (hj : j ≤ (olb_orbitLoop K hK e he).length)
    (hk : k ≤ (olb_orbitLoop K hK e he).length)
    (hij : i < j) (hjk : j < k)
    (hti : ¬ jc4_FootprintFree K ⟨e, he⟩ r i)
    (htk : ¬ jc4_FootprintFree K ⟨e, he⟩ r k) :
    ¬ jc4_FootprintFree K ⟨e, he⟩ r j := by
  
  have hInsideI := hdich.1 i hi hti
  have hInsideK := hdich.1 k hk htk
  
  have hInsideJ := hint i j k hi hj hk hij hjk hInsideI hInsideK
  
  intro hfree
  exact hdich.2 j hj hfree hInsideJ


end Walls
end StatMech
