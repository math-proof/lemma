/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualEventSetEquality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Universality.DualEventSetEquality.Part2
open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

variable {ω : ConfigSpace (Sym2 (Site 2))} {n : ℤ}


noncomputable def des_inducedHom (n : ℤ) (ω : ConfigSpace (Sym2 (Site 2))) :
    (openSubgraphInduce 2 (dualConfig ω) (rect 0 n 0 n)) →g
      (openSubgraphInduce 2 (des_negConfig ω) (rect 0 n (-n) 0)) where
  toFun := fun x => ⟨rot90Inv (x : Site 2), (des_rot90Inv_rect n x).1 x.2⟩
  map_rel' := by
    intro x y hxy
    rw [openSubgraphInduce_adj, openSubgraph_adj] at hxy
    show IsOpenEdge 2 (des_negConfig ω) (rot90Inv (x : Site 2)) (rot90Inv (y : Site 2))
    exact (des_isOpenEdge_dual_iff ω (x : Site 2) (y : Site 2)).1 hxy


noncomputable def des_inducedHomInv (n : ℤ) (ω : ConfigSpace (Sym2 (Site 2))) :
    (openSubgraphInduce 2 (des_negConfig ω) (rect 0 n (-n) 0)) →g
      (openSubgraphInduce 2 (dualConfig ω) (rect 0 n 0 n)) where
  toFun := fun x => ⟨rot90Fun (x : Site 2),
    (des_rot90Inv_rect n (rot90Fun (x : Site 2))).2 (by
      rw [show rot90Inv (rot90Fun (x : Site 2)) = (x : Site 2) from
        rot90Equiv.left_inv (x : Site 2)]; exact x.2)⟩
  map_rel' := by
    intro x y hxy
    rw [openSubgraphInduce_adj, openSubgraph_adj] at hxy
    show IsOpenEdge 2 (dualConfig ω) (rot90Fun (x : Site 2)) (rot90Fun (y : Site 2))
    rw [des_isOpenEdge_dual_iff ω (rot90Fun (x : Site 2)) (rot90Fun (y : Site 2))]
    rw [show rot90Inv (rot90Fun (x : Site 2)) = (x : Site 2) from
        rot90Equiv.left_inv (x : Site 2),
       show rot90Inv (rot90Fun (y : Site 2)) = (y : Site 2) from
        rot90Equiv.left_inv (y : Site 2)]
    exact hxy


end Universality
end StatMech
