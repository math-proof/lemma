/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleSpace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.EulerGeneral
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanCoresUnify.Part2
import Def.StatisticalMechanics.Code.Lattice.JordanCycleSpace.Part2
open SimpleGraph Set List Function


namespace StatMech

namespace Lattice

theorem jcs_cycle_two_components {V : Type*} {G : SimpleGraph V} {v : V}
    (c : G.Walk v v) (hc : c.IsCycle) (S : Set (Site 2)) (hbridge : jcs_GeometricBridge S) :
    faceCount c.toSubgraph.coe = 2 ∧
      Nat.card (latticeMinusBarrier S).ConnectedComponent = 2 :=
  ⟨jcs_cycle_faceCount_eq_two c hc, jcs_two_components_of_region hbridge⟩


theorem jcs_separatingSide_of_bridge {D B inside outside : Set (Site 2)} (S : Set (Site 2))
    (hbridge : jcs_GeometricBridge S)
    (hinS : ∀ z ∈ inside, z ∈ S) (houtS : ∀ z ∈ outside, z ∉ S)
    (hbd : ∀ u v : Site 2, u ∈ D → v ∈ D → (hypercubicLattice 2).Adj u v →
      u ∈ S → v ∉ S → (u ∈ B ∨ v ∈ B)) :
    jcu_HasSeparatingSide D B inside outside ∧
      Nat.card (latticeMinusBarrier S).ConnectedComponent = 2 :=
  ⟨jcs_separatingSide S hinS houtS hbd, jcs_two_components_of_region hbridge⟩


end Lattice
end StatMech
