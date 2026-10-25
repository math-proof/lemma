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
import Def.StatisticalMechanics.Code.Walls.jc8core.Part2
open SimpleGraph Function Set


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem jc8c_touchingConvex_of_residue_windowed (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (r : Site 2)
    (hres : jc8c_InsideIntervalResidue K hK e he r) :
    ∀ i j k, i ≤ (olb_orbitLoop K hK e he).length → j ≤ (olb_orbitLoop K hK e he).length →
      k ≤ (olb_orbitLoop K hK e he).length → i < j → j < k →
      ¬ jc4_FootprintFree K ⟨e, he⟩ r i → ¬ jc4_FootprintFree K ⟨e, he⟩ r k →
      ¬ jc4_FootprintFree K ⟨e, he⟩ r j :=
  fun i j k hi hj hk hij hjk hti htk =>
    jc8c_touchingConvex_window K hK e he r hres.1 hres.2 i j k hi hj hk hij hjk hti htk


end Walls
end StatMech
