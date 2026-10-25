/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopAddedEdgeRooted.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStraightLineDeletion
open scoped BigOperators
open Finset SimpleGraph Filter


namespace StatMech.Onsager

open StatMech.FrontierA

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


def ons_kwAddedEdgeBaseMatrix
    (embedding : KWStraightLineEmbedding G)
    (weight : Sym2 V → Complex) : Matrix G.Dart G.Dart Complex :=
  kwGraphTransition G weight embedding.turnPhase


def ons_kwAddedEdgeRoot
    (embedding : KWStraightLineEmbedding G)
    (weight : Sym2 V → Complex) (selected : G.Dart)
    (t : Complex) : Complex :=
  ons_detWalkRoot
    (kwGraphTransition G
      (kwScaleGraphEdgeWeight weight selected.edge t)
      embedding.turnPhase)


def ons_kwAddedEdgeDeletedRoot
    (embedding : KWStraightLineEmbedding G)
    (weight : Sym2 V → Complex) (selected : G.Dart) : Complex :=
  ons_detWalkRoot
    (ons_maskMatrix ({selected, selected.symm} : Finset G.Dart)
      (ons_kwAddedEdgeBaseMatrix G embedding weight))


def ons_kwAddedEdgeRootedSeries
    (embedding : KWStraightLineEmbedding G)
    (weight : Sym2 V → Complex) (selected : G.Dart) : Complex :=
  ∑' path : List G.Dart,
    ons_firstReturnWeight (ons_kwAddedEdgeBaseMatrix G embedding weight)
      selected selected.symm path


end
end StatMech.Onsager
