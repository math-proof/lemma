/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarDuality
import Def.StatisticalMechanics.Code.FK.TriHexPeriodicDual.Part5
open Finset Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

open Lattice

theorem hexagonalEdgeChart_injective : Function.Injective hexagonalEdgeChart := by
  rintro ⟨x, i⟩ ⟨y, j⟩ h
  have he : s((x, false), (x + hexagonalStep i, true)) =
      s((y, false), (y + hexagonalStep j, true)) := congrArg Subtype.val h
  rw [Sym2.eq_iff] at he
  rcases he with hdir | hswap
  · have hxy : x = y := congrArg Prod.fst hdir.1
    subst y
    have hs0 : x + hexagonalStep i = x + hexagonalStep j :=
      congrArg Prod.fst hdir.2
    have hs : hexagonalStep i = hexagonalStep j := add_left_cancel hs0
    exact Prod.ext rfl (hexagonalStep_injective hs)
  · have hbool : (false : Bool) = true := congrArg Prod.snd hswap.1
    simp at hbool

theorem hexagonalEdgeChart_surjective : Function.Surjective hexagonalEdgeChart := by
  rintro ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
      rw [SimpleGraph.mem_edgeSet, hexagonalGraph_adj, hexagonalAdj] at he
      rcases he with ⟨hu, hv, i, hi⟩ | ⟨hv, hu, i, hi⟩
      · have hvSite : v.1 = u.1 + hexagonalStep i := by
          ext k
          have hk := congrFun hi k
          simp only [Pi.sub_apply, Pi.add_apply] at hk ⊢
          omega
        refine ⟨(u.1, i), Subtype.ext ?_⟩
        apply Sym2.eq_iff.mpr
        left
        constructor
        · exact Prod.ext rfl hu.symm
        · exact Prod.ext hvSite.symm hv.symm
      · have huSite : u.1 = v.1 + hexagonalStep i := by
          ext k
          have hk := congrFun hi k
          simp only [Pi.sub_apply, Pi.add_apply] at hk ⊢
          omega
        refine ⟨(v.1, i), Subtype.ext ?_⟩
        apply Sym2.eq_iff.mpr
        right
        constructor
        · exact Prod.ext rfl hv.symm
        · exact Prod.ext huSite.symm hu.symm


end PeriodicPlanar
end FK
end StatMech
