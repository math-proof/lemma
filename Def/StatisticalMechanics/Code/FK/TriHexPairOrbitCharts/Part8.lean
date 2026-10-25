/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicCrossingGeometry
import Abbrev.StatisticalMechanics.Code.FK.TriHexPairOrbitCharts.Part2
open SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


def hexagonalPairNormal (u v : HexVertex) :
    Site 2 × HexagonalPairShape :=
  if h : siteLexPositive (v.1 - u.1) then
    (u.1, Sum.inl (⟨v.1 - u.1, h⟩, u.2, v.2))
  else if hr : siteLexPositive (u.1 - v.1) then
    (v.1, Sum.inl (⟨u.1 - v.1, hr⟩, v.2, u.2))
  else if hb : boolOrdered u.2 v.2 then
    (u.1, Sum.inr ⟨(u.2, v.2), hb⟩)
  else
    (v.1, Sum.inr ⟨(v.2, u.2), by
      rcases u with ⟨x, b⟩
      rcases v with ⟨y, c⟩
      cases b <;> cases c <;> simp [boolOrdered] at hb ⊢⟩)

end StatMech.FK.PeriodicPlanar
