/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenBoxGeneral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.bgf2faithcontract.Part5
import Def.StatisticalMechanics.Code.FrontierA.AllOpenBoxGeneral.Part3
open Set SimpleGraph Finset


namespace StatMech.FrontierA

open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

open StatMech.Walls

variable {d : ℕ}


theorem bgfd_indexAllOpen_connected
    {omega : ConfigSpace (Sym2 (Site d))} {L : ℕ} {j : Site d}
    (hopen : BgfdIndexAllOpen omega L j) {x y : Site d}
    (hx : bgn_idx L x = j) (hy : bgn_idx L y = j) :
    Connected d omega x y := by
  refine bgfd_box_connected ?_
    (bgfd_idx_iff_inBox.mp hx) (bgfd_idx_iff_inBox.mp hy)
  intro a b ha hb hadj
  exact hopen a b (bgfd_idx_iff_inBox.mpr ha)
    (bgfd_idx_iff_inBox.mpr hb) hadj

end StatMech.FrontierA
