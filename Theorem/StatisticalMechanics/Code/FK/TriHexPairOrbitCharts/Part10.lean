/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicCrossingGeometry
import Def.StatisticalMechanics.Code.FK.TriHexPairOrbitCharts.Part11
open SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


theorem hexagonalPairNormal_add (z : Site 2) (u v : HexVertex) :
    hexagonalPairNormal (hexTranslate z u) (hexTranslate z v) =
      (hexagonalPairNormal u v).map (fun b => b + z) id := by
  rcases u with ⟨x, b⟩
  rcases v with ⟨y, c⟩
  unfold hexagonalPairNormal
  simp only [hexTranslate_apply]
  have hsub : y + z - (x + z) = y - x := by abel
  have hsub' : x + z - (y + z) = x - y := by abel
  simp only [hsub, hsub']
  split_ifs <;> rfl

theorem hexagonalPairOrbitEquiv_add (z : Site 2) (e : Sym2 HexVertex) :
    hexagonalPairOrbitEquiv (Sym2.map (hexTranslate z) e) =
      (hexagonalPairOrbitEquiv e).map (fun b => b + z) id := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [hexagonalPairOrbitEquiv, Equiv.coe_fn_mk,
        Sym2.map_mk, hexagonalPairOrbitTo_mk]
      exact hexagonalPairNormal_add z u v


end StatMech.FK.PeriodicPlanar
