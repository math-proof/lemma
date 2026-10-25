/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf2faithcontract.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.baoallopen.Part2
import Theorem.StatisticalMechanics.Code.Walls.bcvcutvertex.Part3
import Theorem.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
import Theorem.StatisticalMechanics.Code.Walls.bgf2faithcontract.Part4
open Set SimpleGraph Finset
open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation


open Classical in

noncomputable def bgf2_q (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (x : Site 2) : Site 2 :=
  if bgf2_IndexAllOpen ω L (bgn_idx L x) then bgf2_centre L (bgn_idx L x) else x


def bgf2_Gf (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) : SimpleGraph (Site 2) where
  Adj u v := u ≠ v ∧ ∃ a b : Site 2, bgf2_q ω L a = u ∧ bgf2_q ω L b = v ∧ (openSubgraph 2 ω).Adj a b
  symm := by
    constructor
    rintro u v ⟨huv, a, b, ha, hb, hab⟩
    exact ⟨huv.symm, b, a, hb, ha, hab.symm⟩

end StatMech.Walls
