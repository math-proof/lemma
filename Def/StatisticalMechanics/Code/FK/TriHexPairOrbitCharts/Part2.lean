/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicCrossingGeometry
import Abbrev.StatisticalMechanics.Code.FK.TriHexPairOrbitCharts
open SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


def triangularPairNormal (x y : Site 2) :
    Site 2 × TriangularPairShape :=
  if h : siteLexNonnegative (y - x) then (x, ⟨y - x, h⟩)
  else (y, ⟨x - y, by
    have := siteLexNonnegative_neg_of_not h
    simpa only [neg_sub] using this⟩)

end StatMech.FK.PeriodicPlanar
