module
public import Def.StatisticalMechanics.Code.Universality.IsingFermionicMedialComplex.Part7
public import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDuality
public import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part13


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareSideCornerEquiv :
    FKIsingMedialSide ≃
      FKIsingSquareEdgeEndpoint × FKIsingSquareCornerTurn where
  toFun := fkIsingSquareSideCorner
  invFun := fkIsingSquareCornerSide
  left_inv := fkIsingSquareCornerSide_sideCorner
  right_inv := fkIsingSquareSideCorner_cornerSide


def fkIsingSquareDartEndpoint (n : Nat)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (fkSquareBoxPlanar n).V :=
  match (fkIsingSquareSideCorner d.2).1 with
  | .tail => (fkIsingSquareOrientedEdge n d.1).tail
  | .head => (fkIsingSquareOrientedEdge n d.1).head


end
end StatMech.Universality
