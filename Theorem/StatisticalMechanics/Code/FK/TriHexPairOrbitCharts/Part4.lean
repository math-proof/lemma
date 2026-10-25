/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicCrossingGeometry
import Def.StatisticalMechanics.Code.FK.TriHexPairOrbitCharts.Part4
open SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


theorem triangularPairOrbitFrom_to (e : Sym2 (Site 2)) :
    triangularPairOrbitFrom (triangularPairOrbitTo e) = e := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [triangularPairOrbitTo_mk]
      unfold triangularPairNormal triangularPairOrbitFrom
      split_ifs
      · congr 1
        ext k
        simp
      · rw [show y + (x - y) = x by abel]
        exact Sym2.eq_swap

theorem triangularPairOrbitTo_from
    (a : Site 2 × TriangularPairShape) :
    triangularPairOrbitTo (triangularPairOrbitFrom a) = a := by
  rcases a with ⟨x, d, hd⟩
  rw [show triangularPairOrbitFrom (x, ⟨d, hd⟩) = s(x, x + d) by rfl]
  rw [triangularPairOrbitTo_mk]
  unfold triangularPairNormal
  simp only [add_sub_cancel_left, hd, dite_true]


end StatMech.FK.PeriodicPlanar
