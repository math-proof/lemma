/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.AnnulusDefs.Part10
import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Def.StatisticalMechanics.Code.BeffaraDC.SymmetricDomainSelfDuality.Part10
open Finset SimpleGraph
open scoped BigOperators
open StatMech.Lattice


namespace StatMech

namespace BeffaraDC

noncomputable section

namespace SymmetricDomain

theorem mixedConnected_all_of_boundaryBlocksOverlap
    (D : SymmetricDomain) (h : D.BoundaryBlocksOverlap)
    (omega : ConfigSpace (Sym2 D.Vertex)) :
    D.MixedConnected omega := by
  obtain ⟨x, hx₁, hx₂⟩ := h
  exact ⟨x, x, hx₁, hx₂, SimpleGraph.Reachable.rfl⟩


theorem no_mixedDualComplementRN_of_boundaryBlocksOverlap
    (D : SymmetricDomain) (q : Real) (h : D.BoundaryBlocksOverlap) :
    MixedDualComplementRN D q → False := by
  intro R
  let omega : ConfigSpace (Sym2 D.Vertex) := fun _ => false
  have hconnected : D.MixedConnected (R.dual omega) :=
    mixedConnected_all_of_boundaryBlocksOverlap D h _
  have hnot : ¬D.MixedConnected omega :=
    (R.connected_dual_iff omega).mp hconnected
  exact hnot (mixedConnected_all_of_boundaryBlocksOverlap D h omega)


end SymmetricDomain
end
end BeffaraDC
end StatMech
