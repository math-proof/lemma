/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicDual.Part7
import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
import Theorem.StatisticalMechanics.Code.FK.TriHexTorusDuality.Part6
open Finset Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

noncomputable def hexagonalTorusEdgeChartEquiv (L : ℕ) [Fact (2 < L)] :
    TriHexTorusEdgeIndex L ≃ (hexagonalTorusGraph L).edgeSet :=
  Equiv.ofBijective (hexagonalTorusEdgeChart L)
    ⟨hexagonalTorusEdgeChart_injective L, hexagonalTorusEdgeChart_surjective L⟩


def triHexTorusIndexEquiv (L : ℕ) :
    TriHexTorusEdgeIndex L ≃ TriHexTorusEdgeIndex L where
  toFun a := (if a.2 = 2 then a.1 - (1, 0) else a.1, a.2)
  invFun a := (if a.2 = 2 then a.1 + (1, 0) else a.1, a.2)
  left_inv := by
    rintro ⟨z, i⟩
    fin_cases i <;> ext <;> simp
  right_inv := by
    rintro ⟨z, i⟩
    fin_cases i <;> ext <;> simp


noncomputable def triHexTorusDualEdgeEquiv (L : ℕ) [Fact (2 < L)] :
    (triangularTorusGraph L).edgeSet ≃ (hexagonalTorusGraph L).edgeSet :=
  (triangularTorusEdgeChartEquiv L).symm.trans
    ((triHexTorusIndexEquiv L).trans (hexagonalTorusEdgeChartEquiv L))


noncomputable def triHexTorusPrimalOfDualEdge (L : ℕ) [Fact (2 < L)]
    (e : Sym2 (HexTorusVertex L)) : Sym2 (TorusSite L) :=
  if he : e ∈ (hexagonalTorusGraph L).edgeSet then
    ((triHexTorusDualEdgeEquiv L).symm ⟨e, he⟩ :
      (triangularTorusGraph L).edgeSet)
  else s((0, 0), (0, 0))

end PeriodicPlanar
end FK
end StatMech
