module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Walls.jc4_firstreturnK.Part2
public import Theorem.StatisticalMechanics.Code.Walls.jc4_tailnotprobed
public import Theorem.StatisticalMechanics.Code.Walls.jc5_core.Part2
public import Theorem.StatisticalMechanics.Code.Walls.jc7core.Part2
public import Theorem.StatisticalMechanics.Code.Walls.jc7loopiscycle
public import Theorem.StatisticalMechanics.Code.Walls.jc7loopseparates.Part2
public import Theorem.StatisticalMechanics.Code.Walls.jc7ivtnohop
public import Theorem.StatisticalMechanics.Code.Walls.jc7getverteqdartface
public import Theorem.StatisticalMechanics.Code.Walls.jc8touchingfaceband
public import Theorem.StatisticalMechanics.Code.Walls.jc8tworowbands.Part2
public import Theorem.StatisticalMechanics.Code.Walls.jc8crossparityleftregion.Part2
public import Theorem.StatisticalMechanics.Code.Walls.jc8bdedgelandssupport.Part2
public import Theorem.StatisticalMechanics.Code.Walls.jc8cyclenodup
public import Theorem.StatisticalMechanics.Code.Walls.jc8subarcwalk
public import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
public import Theorem.StatisticalMechanics.Code.Lattice.OrbitLoopBridge
public import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
public import Theorem.StatisticalMechanics.Code.Walls.jc8core
open SimpleGraph Function Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8core.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Walls

open StatMech.Lattice


def jc8c_SideDichotomy (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (r : Site 2) : Prop :=
  (∀ j, j ≤ (olb_orbitLoop K hK e he).length → ¬ jc4_FootprintFree K ⟨e, he⟩ r j →
      (olb_orbitLoop K hK e he).getVert j ∈ jec_leftRegion (olb_orbitLoop K hK e he)) ∧
  (∀ j, j ≤ (olb_orbitLoop K hK e he).length → jc4_FootprintFree K ⟨e, he⟩ r j →
      (olb_orbitLoop K hK e he).getVert j ∉ jec_leftRegion (olb_orbitLoop K hK e he))


def jc8c_InsideInterval (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) : Prop :=
  ∀ i j k, i ≤ (olb_orbitLoop K hK e he).length → j ≤ (olb_orbitLoop K hK e he).length →
    k ≤ (olb_orbitLoop K hK e he).length → i < j → j < k →
    (olb_orbitLoop K hK e he).getVert i ∈ jec_leftRegion (olb_orbitLoop K hK e he) →
    (olb_orbitLoop K hK e he).getVert k ∈ jec_leftRegion (olb_orbitLoop K hK e he) →
    (olb_orbitLoop K hK e he).getVert j ∈ jec_leftRegion (olb_orbitLoop K hK e he)


end Walls
end StatMech
