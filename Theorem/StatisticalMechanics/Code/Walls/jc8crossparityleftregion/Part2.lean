/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8crossparityleftregion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.OrbitLoopBridge
import Def.StatisticalMechanics.Code.Walls.jc8crossparityleftregion
open SimpleGraph Function Set


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem jc8_crossParityLeftRegion (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) : jc8_CrossParityLeftRegion K hK e he :=
  ⟨fun S {_x _y} w => jc8_crossCount_parity S w,
   fun {_x _y} w hx hy => jc8_crossCount_ge_one_of_opposite_leftRegion K hK e he w hx hy⟩


theorem jc8_crossCount_parity_self (S : Set (Site 2)) {x : Site 2}
    (w : (hypercubicLattice 2).Walk x x) :
    Even (crossCount S w) :=
  jc8_crossCount_even_of_closed S w


theorem jc8_leftRegion_loop_even (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) :
    Even (crossCount (jec_leftRegion (olb_orbitLoop K hK e he))
      (olb_orbitLoop K hK e he)) :=
  jc8_orbitLoop_crossCount_even K hK e he (jec_leftRegion (olb_orbitLoop K hK e he))


end Walls
end StatMech
