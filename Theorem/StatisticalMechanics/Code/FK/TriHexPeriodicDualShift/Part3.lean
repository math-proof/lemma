/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicDualShift.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicDual.Part7
import Def.StatisticalMechanics.Code.FK.TriHexPeriodicDualShift.Part2
open SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


theorem hexagonalEdgeTranslate_val (z : Site 2)
    (e : hexagonalGraph.edgeSet) :
    ((hexagonalEdgeTranslate z e : hexagonalGraph.edgeSet) : Sym2 HexVertex) =
      Sym2.map (hexTranslate z) (e : Sym2 HexVertex) := by
  let a := hexagonalEdgeChartEquiv.symm e
  have he : hexagonalEdgeChart a = e :=
    hexagonalEdgeChartEquiv.apply_symm_apply e
  change hexagonalIndexedEdge (a.1 + z, a.2) =
    Sym2.map (hexTranslate z) (e : Sym2 HexVertex)
  rw [hexagonalIndexedEdge_add]
  exact congrArg (Sym2.map (hexTranslate z)) (congrArg Subtype.val he)


theorem triHexDualEdgeEquiv_add (z : Site 2)
    (e : triangularGraph.edgeSet) :
    triHexDualEdgeEquiv (triangularEdgeTranslate z e) =
      hexagonalEdgeTranslate z (triHexDualEdgeEquiv e) := by
  let a := triangularEdgeChartEquiv.symm e
  have he : triangularEdgeChart a = e :=
    triangularEdgeChartEquiv.apply_symm_apply e
  apply Subtype.ext
  change ((triHexDualEdgeEquiv
      (triangularEdgeChart (a.1 + z, a.2)) :
        hexagonalGraph.edgeSet) : Sym2 HexVertex) = _
  rw [triHexDualEdgeEquiv_add_chart]
  rw [he]
  exact (hexagonalEdgeTranslate_val z (triHexDualEdgeEquiv e)).symm

end StatMech.FK.PeriodicPlanar
