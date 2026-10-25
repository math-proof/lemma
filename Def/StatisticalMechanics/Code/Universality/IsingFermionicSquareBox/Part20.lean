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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part21


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

noncomputable def fkIsingSquareBondMate (n : Nat) (hn : 0 < n)
    (x : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    FKIsingMedialDart (fkSquareBoxPlanar n) :=
  let u := fkIsingSquareDartEndpoint n x
  let d := fkIsingSquareDartDirection n x
  let hd := fkIsingSquareDartDirection_available n x
  match (fkIsingSquareSideCorner x.2).2 with
  | .counterclockwise =>
      fkIsingSquareDirectionDart n u
        (fkIsingSquareNextDirection n u d)
        (fkIsingSquareNextDirection_available n hn u d hd) .clockwise
  | .clockwise =>
      fkIsingSquareDirectionDart n u
        (fkIsingSquarePreviousDirection n u d)
        (fkIsingSquarePreviousDirection_available n hn u d hd)
        .counterclockwise

end
end StatMech.Universality
