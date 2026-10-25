/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcscornersum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.wadangledefect.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Theorem.StatisticalMechanics.Code.Lattice.GaussBonnet.Part4
import Theorem.StatisticalMechanics.Code.Walls.jc5_singlecycle.Part2
import Theorem.StatisticalMechanics.Code.Walls.wcscornersum.Part4
open scoped BigOperators
open Finset
open SimpleGraph Function


namespace StatMech

namespace Wcs

open StatMech.Lattice

open StatMech.Wad

open StatMech.Euc

open StatMech.Walls


noncomputable def posPartSite (z : Site 2) : Site 2 := ![max (z 0) 0, max (z 1) 0]


noncomputable def wcs_pivotSite (e : Dart) : Site 2 :=
  e.tail + posPartSite e.dir + posPartSite (-rot90Fun e.dir)


noncomputable def wcs_pivot (e : Dart) : ℤ × ℤ := siteToVtx (wcs_pivotSite e)


end Wcs
end StatMech
