/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxOffCentre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.CenteredFirstHit
import Theorem.StatisticalMechanics.Code.OSSS.WiredBoxLocalized.Part3
import Theorem.StatisticalMechanics.Code.FK.OffCentreDomination.Part13
import Theorem.StatisticalMechanics.Code.FK.CylinderDecayClose.Part6
import Theorem.StatisticalMechanics.Code.OSSS.WiredBoxOffCentre.Part3
open scoped BigOperators Classical


namespace StatMech

namespace OSSS

namespace WiredBoxOffCentre

open Lattice IsingFK RevealmentConstruction TreeComplete RevealmentTranslation CenteredFirstHit

open FK

open WiredBoxLocalized

noncomputable def centeredWithinToTransHom
    (d n k : Nat) (x : Site d)
    (hsub : fvs_transBox d (2 * k) x ⊆ box d (2 * n))
    (rho : ConfigSpace (Sym2 (boxVerts d (2 * n)))) :
    openSubgraphInduce d (extendEdge d (2 * n) rho) (centeredClosedBox x k) →g
      openSub (fvs_transBoxGraph d (2 * k) x)
        (ocd_innerRestrict (flc_incl hsub) rho) where
  toFun := fun y => ⟨(y : Site d), by
    show ((y : Site d) - x) ∈ box d (2 * k)
    rw [mem_box_iff_siteRadius_le]
    change centeredRadius x (y : Site d) <= 2 * k
    exact y.2.trans (by omega)⟩
  map_rel' := by
    intro y z hyz
    rw [openSubgraphInduce_adj, openSubgraph_adj] at hyz
    rw [openSub_adj]
    refine ⟨by
      rw [fvs_transBoxGraph, SimpleGraph.comap_adj]
      exact hyz.1, ?_⟩
    let be : Sym2 (boxVerts d (2 * n)) :=
      Sym2.map (flc_incl hsub) s(⟨(y : Site d), by
        show ((y : Site d) - x) ∈ box d (2 * k)
        rw [mem_box_iff_siteRadius_le]
        change centeredRadius x (y : Site d) <= 2 * k
        exact y.2.trans (by omega)⟩,
        ⟨(z : Site d), by
          show ((z : Site d) - x) ∈ box d (2 * k)
          rw [mem_box_iff_siteRadius_le]
          change centeredRadius x (z : Site d) <= 2 * k
          exact z.2.trans (by omega)⟩)
    have hbe : edgeIncl d (2 * n) be = s((y : Site d), (z : Site d)) := by
      unfold be edgeIncl
      rw [Sym2.map_map, Sym2.map_mk]
      rfl
    have hopen := hyz.2
    rw [← hbe, extendEdge_eq_of_range] at hopen
    exact hopen

end WiredBoxOffCentre
end OSSS
end StatMech
