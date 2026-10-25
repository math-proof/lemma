/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MatchedPlanarDualityClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
import Theorem.StatisticalMechanics.Code.Universality.DualEventSetEquality.Part4
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomy
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomyClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.JordanExhaustivityClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.RSWFrameReconcileClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.MatchedPlanarDualityClose
open Set SimpleGraph Finset
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

noncomputable def mpd_inducedHom (a b c d : ℤ) (ω : ConfigSpace (Sym2 (Site 2))) :
    (openSubgraphInduce 2 (dualConfig ω) (rect a b c d)) →g
      (openSubgraphInduce 2 (des_negConfig ω) (rect c d (-b) (-a))) where
  toFun := fun x => ⟨rot90Inv (x : Site 2), (mpd_rot90Inv_rect a b c d x).1 x.2⟩
  map_rel' := by
    intro x y hxy
    rw [openSubgraphInduce_adj, openSubgraph_adj] at hxy
    change IsOpenEdge 2 (des_negConfig ω) (rot90Inv (x : Site 2)) (rot90Inv (y : Site 2))
    exact (des_isOpenEdge_dual_iff ω (x : Site 2) (y : Site 2)).1 hxy


noncomputable def mpd_inducedHomInv (a b c d : ℤ) (ω : ConfigSpace (Sym2 (Site 2))) :
    (openSubgraphInduce 2 (des_negConfig ω) (rect c d (-b) (-a))) →g
      (openSubgraphInduce 2 (dualConfig ω) (rect a b c d)) where
  toFun := fun x => ⟨rot90Fun (x : Site 2),
    (mpd_rot90Inv_rect a b c d (rot90Fun (x : Site 2))).2 (by
      rw [show rot90Inv (rot90Fun (x : Site 2)) = (x : Site 2) from
        rot90Equiv.left_inv (x : Site 2)]; exact x.2)⟩
  map_rel' := by
    intro x y hxy
    rw [openSubgraphInduce_adj, openSubgraph_adj] at hxy
    change IsOpenEdge 2 (dualConfig ω) (rot90Fun (x : Site 2)) (rot90Fun (y : Site 2))
    rw [des_isOpenEdge_dual_iff ω (rot90Fun (x : Site 2)) (rot90Fun (y : Site 2))]
    rw [show rot90Inv (rot90Fun (x : Site 2)) = (x : Site 2) from rot90Equiv.left_inv (x : Site 2),
       show rot90Inv (rot90Fun (y : Site 2)) = (y : Site 2) from rot90Equiv.left_inv (y : Site 2)]
    exact hxy


end Universality
end StatMech
