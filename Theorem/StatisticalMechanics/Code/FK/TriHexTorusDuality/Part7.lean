/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicDual.Part7
import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
import Def.StatisticalMechanics.Code.FK.TriHexTorusDuality.Part6
open Finset Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

theorem triHexTorusPrimalOfDualEdge_mem (L : ℕ) [Fact (2 < L)]
    {e : Sym2 (HexTorusVertex L)}
    (he : e ∈ (hexagonalTorusGraph L).edgeFinset) :
    triHexTorusPrimalOfDualEdge L e ∈
      (triangularTorusGraph L).edgeFinset := by
  have heSet : e ∈ (hexagonalTorusGraph L).edgeSet := by
    simpa [SimpleGraph.edgeFinset] using he
  simp only [triHexTorusPrimalOfDualEdge, dif_pos heSet]
  change (((triHexTorusDualEdgeEquiv L).symm ⟨e, heSet⟩ :
    (triangularTorusGraph L).edgeSet) : Sym2 (TorusSite L)) ∈
      (triangularTorusGraph L).edgeSet.toFinset
  rw [Set.mem_toFinset]
  exact ((triHexTorusDualEdgeEquiv L).symm ⟨e, heSet⟩).2

theorem triHexTorusPrimalOfDualEdge_injOn (L : ℕ) [Fact (2 < L)] :
    Set.InjOn (triHexTorusPrimalOfDualEdge L)
      (↑(hexagonalTorusGraph L).edgeFinset :
        Set (Sym2 (HexTorusVertex L))) := by
  intro e he e' he' h
  have heSet : e ∈ (hexagonalTorusGraph L).edgeSet := by
    simpa [SimpleGraph.edgeFinset] using he
  have heSet' : e' ∈ (hexagonalTorusGraph L).edgeSet := by
    simpa [SimpleGraph.edgeFinset] using he'
  simp only [triHexTorusPrimalOfDualEdge, dif_pos heSet, dif_pos heSet'] at h
  exact congrArg Subtype.val ((triHexTorusDualEdgeEquiv L).symm.injective
    (Subtype.ext h))


end PeriodicPlanar
end FK
end StatMech
