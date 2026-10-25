/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcddefectbridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.wadangledefect.Part4
import Theorem.StatisticalMechanics.Code.Walls.jc5_singlecycle.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Theorem.StatisticalMechanics.Code.Lattice.BalanceContraction.Part2
import Theorem.StatisticalMechanics.Code.Lattice.GaussBonnet.Part4
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
import Theorem.StatisticalMechanics.Code.Walls.wcddefectbridge.Part3
open scoped BigOperators
open Finset
open SimpleGraph Function


namespace StatMech

namespace Wcd

open StatMech.Lattice

open StatMech.Wad

open StatMech.Euc


noncomputable def wcd_posPartSite (z : Site 2) : Site 2 := ![max (z 0) 0, max (z 1) 0]


noncomputable def wcd_pivotSite (e : Dart) : Site 2 :=
  e.tail + wcd_posPartSite e.dir + wcd_posPartSite (-rot90Fun e.dir)


noncomputable def wcd_pivot (e : Dart) : ℤ × ℤ := wcd_siteToVtx (wcd_pivotSite e)


end Wcd
end StatMech
