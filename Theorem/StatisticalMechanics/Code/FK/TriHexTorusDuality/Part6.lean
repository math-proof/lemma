/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicDual.Part7
import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
import Def.StatisticalMechanics.Code.FK.TriHexTorusDuality.Part5
open Finset Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

theorem hexagonalTorusEdgeChart_injective (L : ℕ) [Fact (2 < L)] :
    Function.Injective (hexagonalTorusEdgeChart L) := by
  rintro ⟨x, i⟩ ⟨y, j⟩ h
  have he : s((x, false), (x + hexagonalTorusStep L i, true)) =
      s((y, false), (y + hexagonalTorusStep L j, true)) :=
    congrArg Subtype.val h
  rw [Sym2.eq_iff] at he
  rcases he with hdir | hswap
  · have hxy : x = y := congrArg Prod.fst hdir.1
    subst y
    have hs0 : x + hexagonalTorusStep L i =
        x + hexagonalTorusStep L j := congrArg Prod.fst hdir.2
    exact Prod.ext rfl (hexagonalTorusStep_injective L (add_left_cancel hs0))
  · have hb : (false : Bool) = true := congrArg Prod.snd hswap.1
    simp at hb

theorem hexagonalTorusEdgeChart_surjective (L : ℕ) [Fact (2 < L)] :
    Function.Surjective (hexagonalTorusEdgeChart L) := by
  rintro ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
      rw [SimpleGraph.mem_edgeSet] at he
      obtain ⟨a, ha⟩ := he
      exact ⟨a, Subtype.ext ha⟩


end PeriodicPlanar
end FK
end StatMech
