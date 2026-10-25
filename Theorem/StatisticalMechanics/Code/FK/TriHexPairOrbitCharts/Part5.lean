/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicCrossingGeometry
import Def.StatisticalMechanics.Code.FK.TriHexPairOrbitCharts.Part5
open SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


theorem triangularPairNormal_add (z x y : Site 2) :
    triangularPairNormal (x + z) (y + z) =
      (triangularPairNormal x y).map (fun b => b + z) id := by
  unfold triangularPairNormal
  have hsub : y + z - (x + z) = y - x := by abel
  have hsub' : x + z - (y + z) = x - y := by abel
  simp only [hsub, hsub']
  split_ifs <;> rfl

theorem triangularPairOrbitEquiv_add (z : Site 2)
    (e : Sym2 (Site 2)) :
    triangularPairOrbitEquiv (Sym2.map (siteTranslate z) e) =
      (triangularPairOrbitEquiv e).map (fun b => b + z) id := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      simp only [triangularPairOrbitEquiv, Equiv.coe_fn_mk,
        Sym2.map_mk, siteTranslate_apply, triangularPairOrbitTo_mk]
      exact triangularPairNormal_add z x y


end StatMech.FK.PeriodicPlanar
