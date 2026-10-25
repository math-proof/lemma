/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryCancellation.Part7


namespace StatMech.Universality

open Finset Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquarePerimeterPrimalEdgeFinset (n : Nat) :
    Finset (Sym2 (fkSquareBoxPlanar n).V) :=
  Finset.univ.biUnion fun side : FKIsingSquareBoundarySide =>
    Finset.univ.image fun k : Fin (2 * n) =>
      (fkIsingSquarePerimeterEdge n side k).1


def fkIsingSquareClosePerimeter (n : Nat)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    ConfigSpace (Sym2 (fkSquareBoxPlanar n).V) :=
  fun e => if e ∈ fkIsingSquarePerimeterPrimalEdgeFinset n then false
    else omega e

end
end StatMech.Universality
