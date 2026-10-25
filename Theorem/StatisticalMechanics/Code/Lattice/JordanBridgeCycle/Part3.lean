/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanSeparationFinish.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
import Def.StatisticalMechanics.Code.Lattice.JordanBridgeCycle.Part2
open SimpleGraph Set


namespace StatMech

namespace Lattice

@[simp] theorem jbc_rotIso_apply (H : SimpleGraph (Site 2)) (a : Site 2) :
    jbc_rotIso H a = rot90Fun a := rfl


theorem jbc_regionGraph_reachable_iff (H : SimpleGraph (Site 2)) (a b : Site 2) :
    (regionGraph H).Reachable (rot90Fun a) (rot90Fun b) ↔
      (jbc_latticeMinusEdges H).Reachable a b := by
  constructor
  · intro h
    have := h.map (jbc_rotIso H).symm.toHom
    simpa [jbc_rotIso, jbc_rot90Inv_rot90Fun] using this
  · intro h
    have := h.map (jbc_rotIso H).toHom
    simpa [jbc_rotIso] using this


theorem jbc_deleteRegion_le_lattice (H : SimpleGraph (Site 2)) (e : Set (Sym2 (Site 2))) :
    (regionGraph H).deleteEdges e ≤ hypercubicLattice 2 := by
  intro a b hab
  exact hab.1.1


theorem jbc_deleteRegion_eq_pushSup (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) {x y : P.V}
    (hne : x ≠ y) :
    (regionGraph (jei_pushGraph P K)).deleteEdges {crossEdge s(P.emb x, P.emb y)}
      = regionGraph (jei_pushGraph P (K ⊔ edge x y)) := by
  rw [jei_pushGraph_sup_edge P K x y hne]
  rw [jsf_regionGraph_sup_edge (jei_pushGraph P K) (fun h => hne (P.emb.injective h))]


theorem jbc_dualSide_iff_primalAvoid (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) {x y : P.V}
    (hne : x ≠ y) :
    ((regionGraph (jei_pushGraph P K)).deleteEdges
        {crossEdge s(P.emb x, P.emb y)}).Reachable (rot90Fun (P.emb x)) (rot90Fun (P.emb y))
      ↔ (jbc_latticeMinusEdges (jei_pushGraph P (K ⊔ edge x y))).Reachable
          (P.emb x) (P.emb y) := by
  rw [jbc_deleteRegion_eq_pushSup P K hne, jbc_regionGraph_reachable_iff]


end Lattice
end StatMech
