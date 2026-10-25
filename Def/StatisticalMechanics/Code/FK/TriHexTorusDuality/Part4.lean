/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicDual.Part7
import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
import Theorem.StatisticalMechanics.Code.FK.TriHexTorusDuality.Part4
open Finset Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

noncomputable def triangularTorusEdgeChartEquiv (L : ℕ) [Fact (2 < L)] :
    TriHexTorusEdgeIndex L ≃ (triangularTorusGraph L).edgeSet :=
  Equiv.ofBijective (triangularTorusEdgeChart L)
    ⟨triangularTorusEdgeChart_injective L, triangularTorusEdgeChart_surjective L⟩


def hexagonalTorusIndexedEdge (L : ℕ) (a : TriHexTorusEdgeIndex L) :
    Sym2 (HexTorusVertex L) :=
  s((a.1, false), (a.1 + hexagonalTorusStep L a.2, true))


def hexagonalTorusGraph (L : ℕ) [Fact (2 < L)] :
    SimpleGraph (HexTorusVertex L) where
  Adj u v := ∃ a : TriHexTorusEdgeIndex L,
    hexagonalTorusIndexedEdge L a = s(u, v)
  symm := by
    constructor
    rintro u v ⟨a, h⟩
    exact ⟨a, h.trans Sym2.eq_swap⟩
  loopless := ⟨by
    rintro u ⟨a, h⟩
    rw [hexagonalTorusIndexedEdge, Sym2.eq_iff] at h
    rcases h with h | h
    · have hb : (false : Bool) = true := congrArg Prod.snd (h.1.trans h.2.symm)
      simp at hb
    · have hb : (false : Bool) = true := congrArg Prod.snd (h.1.trans h.2.symm)
      simp at hb⟩

end PeriodicPlanar
end FK
end StatMech
