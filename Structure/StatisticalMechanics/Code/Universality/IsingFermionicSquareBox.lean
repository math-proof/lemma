/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicMedialComplex.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDuality
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Mathlib.Combinatorics.SimpleGraph.Matching
import Inductive.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part3


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

structure FKIsingSquareEdgeOrientation (n : Nat)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) where
  tail : (fkSquareBoxPlanar n).V
  head : (fkSquareBoxPlanar n).V
  edge_eq : s(tail, head) = e.1
  axis : FKIsingSquareEdgeAxis
  step : match axis with
    | .horizontal => head.1 = tail.1 + ![1, 0]
    | .vertical => head.1 = tail.1 + ![0, 1]


end
end StatMech.Universality
