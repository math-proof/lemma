module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryCancellation.Part7
public import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayer


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayer.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open Finset Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

@[simp] theorem fkIsingSquareClosePerimeter_perimeterEdge
    (n : Nat) (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    fkIsingSquareClosePerimeter n omega
        (fkIsingSquarePerimeterEdge n side k).1 = false := by
  simp [fkIsingSquareClosePerimeter,
    fkIsingSquarePerimeterPrimalEdgeFinset]

theorem setClosed_fkIsingSquareClosePerimeter_perimeterEdge
    (n : Nat) (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    setClosed (fkIsingSquarePerimeterEdge n side k).1
        (fkIsingSquareClosePerimeter n omega) =
      fkIsingSquareClosePerimeter n omega := by
  funext e
  by_cases h : e = (fkIsingSquarePerimeterEdge n side k).1
  · subst e
    simp [setClosed, fkIsingSquareClosePerimeter_perimeterEdge]
  · simp [setClosed, h]


end
end StatMech.Universality
