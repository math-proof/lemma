/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFamilyAssign.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexContourDecomp.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Def.StatisticalMechanics.Code.Universality.HexFamilyAssign


namespace StatMech.Universality

open Complex

open scoped BigOperators


theorem hexFam_straightSide_dir {V : Type*} [DecidableEq V] (D : HexDomain V)
    (heading : V → Fin 3 → ℤ)
    (hgeom : ∀ v j, D.mid v j - D.pos v = (1 / 2 : ℂ) * hexUnit (heading v j))
    (s : Finset (HexIncidence V)) (h : ℤ)
    (hconst : ∀ e ∈ s, heading e.vtx e.edge = h) :
    ∀ e ∈ s, D.mid e.vtx e.edge - D.pos e.vtx = (1 / 2 : ℂ) * hexUnit h := by
  intro e he
  rw [hgeom e.vtx e.edge, hconst e he]


end StatMech.Universality
