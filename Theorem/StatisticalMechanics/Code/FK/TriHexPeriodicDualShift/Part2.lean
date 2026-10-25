/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicDualShift.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicDual.Part7
import Def.StatisticalMechanics.Code.FK.TriHexPeriodicDualShift
open SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


theorem triangularEdgeTranslate_val (z : Site 2)
    (e : triangularGraph.edgeSet) :
    ((triangularEdgeTranslate z e : triangularGraph.edgeSet) : Sym2 (Site 2)) =
      Sym2.map (siteTranslate z) (e : Sym2 (Site 2)) := by
  let a := triangularEdgeChartEquiv.symm e
  have he : triangularEdgeChart a = e :=
    triangularEdgeChartEquiv.apply_symm_apply e
  change triangularIndexedEdge (a.1 + z, a.2) =
    Sym2.map (siteTranslate z) (e : Sym2 (Site 2))
  rw [triangularIndexedEdge_add]
  exact congrArg (Sym2.map (siteTranslate z)) (congrArg Subtype.val he)


end StatMech.FK.PeriodicPlanar
