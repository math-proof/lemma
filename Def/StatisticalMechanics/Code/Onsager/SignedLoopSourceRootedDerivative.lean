/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopSourceRootedDerivative.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopAddedEdgeRooted
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopHighTempResummation.Part7
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopSourceRootedDerivative
open scoped BigOperators
open Filter SimpleGraph


namespace StatMech.Onsager

open StatMech.FrontierA

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


def ons_kwAddedEdgeEvenBase
    (weight : Sym2 V -> Complex) (selected : G.Dart) : Complex :=
  kwEvenPolynomial G
    (kwScaleGraphEdgeWeight weight selected.edge 0)


def ons_kwAddedEdgeEvenSource
    (weight : Sym2 V -> Complex) (selected : G.Dart) : Complex :=
  weight selected.edge *
    ons_kwEvenEdgeCoefficient G weight selected.edge


def ons_kwAddedEdgeNormalizedSource
    (embedding : KWStraightLineEmbedding G)
    (weight : Sym2 V -> Complex) (selected : G.Dart) : Complex :=
  ons_kwAddedEdgeEvenBase G weight selected /
      ons_kwAddedEdgeRoot G embedding weight selected 0 *
    ons_kwAddedEdgeEvenSource G weight selected


end
end StatMech.Onsager
