/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarDuality
import Def.StatisticalMechanics.Code.FK.TriHexPeriodicDual.Part2
open Finset Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

open Lattice

theorem triangularEdgeChart_injective : Function.Injective triangularEdgeChart := by
  rintro ⟨x, i⟩ ⟨y, j⟩ h
  have he : s(x, x + triangularStep i) = s(y, y + triangularStep j) :=
    congrArg Subtype.val h
  rw [Sym2.eq_iff] at he
  rcases he with hdir | hswap
  · have hxy : x = y := hdir.1
    subst y
    have hs : triangularStep i = triangularStep j :=
      add_left_cancel hdir.2
    exact Prod.ext rfl (triangularStep_injective hs)
  · have hsecond := hswap.2
    rw [hswap.1] at hsecond
    have hzero : triangularStep j + triangularStep i = 0 := by
      apply add_left_cancel (a := y)
      simpa [add_assoc] using hsecond
    exact (triangularStep_add_ne_zero j i hzero).elim

theorem triangularEdgeChart_surjective : Function.Surjective triangularEdgeChart := by
  rintro ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [SimpleGraph.mem_edgeSet, triangularGraph_adj, triangularAdj] at he
      obtain ⟨i, h | h⟩ := he
      · have hy : y = x + triangularStep i := by
          ext k
          have hk := congrFun h k
          simp only [Pi.sub_apply, Pi.add_apply] at hk ⊢
          omega
        refine ⟨(x, i), Subtype.ext ?_⟩
        simp [triangularEdgeChart, triangularIndexedEdge, hy]
      · have hx : x = y + triangularStep i := by
          ext k
          have hk := congrFun h k
          simp only [Pi.sub_apply, Pi.add_apply] at hk ⊢
          omega
        refine ⟨(y, i), Subtype.ext ?_⟩
        simp [triangularEdgeChart, triangularIndexedEdge, hx]


end PeriodicPlanar
end FK
end StatMech
