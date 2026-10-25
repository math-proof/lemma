/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicDual.Part7
import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
import Theorem.StatisticalMechanics.Code.FK.TriHexTorusDuality.Part2
open Finset Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

def triangularTorusIndexedEdge (L : ℕ) (a : TriHexTorusEdgeIndex L) :
    Sym2 (TorusSite L) :=
  s(a.1, a.1 + triangularTorusStep L a.2)


def triangularTorusGraph (L : ℕ) [Fact (2 < L)] : SimpleGraph (TorusSite L) where
  Adj x y := ∃ a : TriHexTorusEdgeIndex L,
    triangularTorusIndexedEdge L a = s(x, y)
  symm := by
    constructor
    rintro x y ⟨a, h⟩
    exact ⟨a, h.trans Sym2.eq_swap⟩
  loopless := ⟨by
    rintro x ⟨⟨z, i⟩, h⟩
    rw [triangularTorusIndexedEdge, Sym2.eq_iff] at h
    rcases h with h | h
    · obtain ⟨hleft, hright⟩ := h
      apply triangularTorusStep_ne_zero L i
      have hz : z + triangularTorusStep L i = z + 0 := by
        rw [hleft] at hright
        simpa using hright
      exact add_left_cancel hz
    · obtain ⟨hleft, hright⟩ := h
      apply triangularTorusStep_ne_zero L i
      have hz : z + triangularTorusStep L i = z + 0 := by
        rw [hleft] at hright
        simpa using hright
      exact add_left_cancel hz⟩

end PeriodicPlanar
end FK
end StatMech
