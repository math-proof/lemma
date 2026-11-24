module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
public import Theorem.StatisticalMechanics.Code.Lattice.OrbitLoopBridge
public import Theorem.StatisticalMechanics.Code.Walls.jc8crossparityleftregion
open SimpleGraph Function Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8crossparityleftregion.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Walls

open StatMech.Lattice


def jc8_CrossParityLeftRegion (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) : Prop :=
  (∀ (S : Set (Site 2)) {x y : Site 2} (w : (hypercubicLattice 2).Walk x y),
      Even (crossCount S w) ↔ (x ∈ S ↔ y ∈ S)) ∧
  (∀ {x y : Site 2} (w : (hypercubicLattice 2).Walk x y),
      x ∈ jec_leftRegion (olb_orbitLoop K hK e he) →
      y ∉ jec_leftRegion (olb_orbitLoop K hK e he) →
      1 ≤ crossCount (jec_leftRegion (olb_orbitLoop K hK e he)) w)


end Walls
end StatMech
