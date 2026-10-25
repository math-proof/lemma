/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7loopseparates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.OrbitEncloses.Part4
import Theorem.StatisticalMechanics.Code.Lattice.OrbitLoopBridge
import Theorem.StatisticalMechanics.Code.Walls.jc6_singlecycle.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc7loopseparates
open SimpleGraph Function Set


namespace StatMech

namespace Walls

open StatMech.Lattice


def jc7_LoopSeparates (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) : Prop :=
  (∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
    u ∉ (olb_orbitLoop K hK e he).support →
    v ∉ (olb_orbitLoop K hK e he).support →
    (Even (jec_rayCount u (olb_orbitLoop K hK e he)) ↔
      Even (jec_rayCount v (olb_orbitLoop K hK e he)))) ∧
  (∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
    bdEdge (jec_leftRegion (olb_orbitLoop K hK e he)) s(u, v) →
    u ∈ (olb_orbitLoop K hK e he).support ∨ v ∈ (olb_orbitLoop K hK e he).support)


end Walls
end StatMech
