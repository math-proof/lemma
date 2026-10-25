/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicMarkedEndpointTraceProjection.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFullSquareBoundaryProjectionGeometry


namespace StatMech.Universality

open Filter Metric Set

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

def fullSquareVertexBoundaryProjection
    (n : Nat) (scale : Real) (x : FKIsingSquareFullVertexNode n) : Complex :=
  fullSquareScaledVertexEmbedding n scale x


def fullSquareFaceFixedBoundaryProjection
    (n : Nat) (scale : Real) (c : FKIsingSquareFullFaceNode n) : Complex :=
  let z := fullSquareScaledFaceEmbedding n scale c
  if c.2.1 = 0 then
    z + ((scale / 2 : Real) : Complex) * (-1 + Complex.I)
  else if c.1.1 + 1 = 2 * n then
    z + ((scale / 2 : Real) : Complex) * (1 + Complex.I)
  else
    z + ((scale / 2 : Real) : Complex) * (1 - Complex.I)


def fullSquareVertexFreeBoundaryProjection
    (n : Nat) (scale : Real) (x : FKIsingSquareFullVertexNode n) : Complex :=
  fullSquareScaledVertexEmbedding n scale x


def fullSquareFaceFreeBoundaryProjection
    (n : Nat) (scale : Real) (c : FKIsingSquareFullFaceNode n) : Complex :=
  fullSquareScaledFaceEmbedding n scale c +
    ((scale / 2 : Real) : Complex) * (-1 - Complex.I)


def fullSquareScaledLeftSide (n : Nat) (scale : Real) : Set Complex :=
  {z | z.re + z.im = -2 * (n : Real) * scale}


def fullSquareScaledBottomSide (n : Nat) (scale : Real) : Set Complex :=
  {z | z.re - z.im = -2 * (n : Real) * scale}


def fullSquareScaledRightSide (n : Nat) (scale : Real) : Set Complex :=
  {z | z.re + z.im = 2 * (n : Real) * scale}


def fullSquareScaledTopSide (n : Nat) (scale : Real) : Set Complex :=
  {z | z.re - z.im = 2 * (n : Real) * scale}

def fullSquareScaledFreeSides (n : Nat) (scale : Real) : Set Complex :=
  fullSquareScaledBottomSide n scale ∪
    fullSquareScaledRightSide n scale ∪ fullSquareScaledTopSide n scale

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
