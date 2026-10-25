/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarDuality
import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicDual.Part6
open Finset Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

open Lattice

noncomputable def hexagonalEdgeChartEquiv :
    TriHexEdgeIndex ≃ hexagonalGraph.edgeSet :=
  Equiv.ofBijective hexagonalEdgeChart
    ⟨hexagonalEdgeChart_injective, hexagonalEdgeChart_surjective⟩


def triHexIndexEquiv : TriHexEdgeIndex ≃ TriHexEdgeIndex where
  toFun a := (if a.2 = 2 then a.1 - triangularStep 0 else a.1, a.2)
  invFun a := (if a.2 = 2 then a.1 + triangularStep 0 else a.1, a.2)
  left_inv := by
    rintro ⟨z, i⟩
    fin_cases i <;> ext <;> simp
  right_inv := by
    rintro ⟨z, i⟩
    fin_cases i <;> ext <;> simp


noncomputable def triHexDualEdgeEquiv :
    triangularGraph.edgeSet ≃ hexagonalGraph.edgeSet :=
  triangularEdgeChartEquiv.symm.trans
    (triHexIndexEquiv.trans hexagonalEdgeChartEquiv)


def triangularFace (u : HexVertex) : Finset (Site 2) :=
  if u.2 then
    {u.1, u.1 - triangularStep 0, u.1 - triangularStep 1}
  else
    {u.1, u.1 + triangularStep 0, u.1 + triangularStep 1}


def incidentHexFaces (a : TriHexEdgeIndex) : HexVertex × HexVertex :=
  let b := triHexIndexEquiv a
  ((b.1, false), (b.1 + hexagonalStep b.2, true))

end PeriodicPlanar
end FK
end StatMech
