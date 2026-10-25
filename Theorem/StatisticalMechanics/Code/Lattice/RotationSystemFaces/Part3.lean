/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RotationSystemFaces.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.InsideConnected.Part2
import Theorem.StatisticalMechanics.Code.Lattice.FaceComponentBijection.Part2
import Def.StatisticalMechanics.Code.Lattice.RotationSystemFaces.Part2
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

@[simp] theorem rsf_componentDarts_mk {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (v : {z : Site 2 // z ∉ Vc.support}) :
    rsf_componentDarts Vc ((fcb_offComplGraph Vc).connectedComponentMk v)
      = {e : Dart | IsBoundaryDart (offSupportComponent Vc (v : Site 2)) e} := rfl


theorem rsf_componentDarts_injective {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) :
    Function.Injective (rsf_componentDarts Vc) := by
  refine ConnectedComponent.ind₂ ?_
  intro u v huv
  rw [rsf_componentDarts_mk, rsf_componentDarts_mk] at huv
  rw [ConnectedComponent.eq]
  apply rsf_fcb_reachable_of_offSupportComponent_eq Vc
  
  obtain ⟨e, he⟩ := rsf_offSupportComponent_exists_boundaryDart Vc u.2
  have heU : e ∈ {e : Dart | IsBoundaryDart (offSupportComponent Vc (u : Site 2)) e} := he
  rw [huv] at heU
  exact rsf_boundaryDart_unique_component Vc he heU


theorem rsf_componentCount_le_facialOrbitRange {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) :
    Nat.card (fcb_offComplGraph Vc).ConnectedComponent
      = Nat.card (Set.range (rsf_componentDarts Vc)) :=
  (Nat.card_range_of_injective (rsf_componentDarts_injective Vc)).symm


end Lattice
end StatMech
