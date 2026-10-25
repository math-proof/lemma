/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicDual.Part7
import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
import Def.StatisticalMechanics.Code.FK.TriHexTorusDuality.Part3
open Finset Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

theorem triangularTorusEdgeChart_injective (L : ℕ) [Fact (2 < L)] :
    Function.Injective (triangularTorusEdgeChart L) := by
  rintro ⟨x, i⟩ ⟨y, j⟩ h
  have he : s(x, x + triangularTorusStep L i) =
      s(y, y + triangularTorusStep L j) := congrArg Subtype.val h
  rw [Sym2.eq_iff] at he
  rcases he with hdir | hswap
  · have hxy : x = y := hdir.1
    subst y
    have hs : triangularTorusStep L i = triangularTorusStep L j :=
      add_left_cancel hdir.2
    exact Prod.ext rfl (triangularTorusStep_injective L hs)
  · have hsecond := hswap.2
    rw [hswap.1] at hsecond
    have hzero : triangularTorusStep L j + triangularTorusStep L i = 0 := by
      apply add_left_cancel (a := y)
      simpa [add_assoc] using hsecond
    exact (triangularTorusStep_add_ne_zero L j i hzero).elim

theorem triangularTorusEdgeChart_surjective (L : ℕ) [Fact (2 < L)] :
    Function.Surjective (triangularTorusEdgeChart L) := by
  rintro ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [SimpleGraph.mem_edgeSet] at he
      obtain ⟨a, ha⟩ := he
      exact ⟨a, Subtype.ext ha⟩


end PeriodicPlanar
end FK
end StatMech
