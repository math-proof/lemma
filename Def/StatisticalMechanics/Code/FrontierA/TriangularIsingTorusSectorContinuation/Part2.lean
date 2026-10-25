/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSectorContinuation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSectors.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonGlobalReduction.Part6
import Instance.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSectorContinuation
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager

noncomputable def triangularTorusEdgeWeight
    (L : Nat) (t1 t2 t3 : Complex) :
    Sym2 (ZMod L × ZMod L) → Complex :=
  fun edge =>
    if squareTorusHorizontalEdge L edge then t1
    else if triangularTorusVerticalEdge L edge then t2
    else t3

noncomputable def triangularTorusSpinScalePolynomial
    (L : Nat) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → Complex)
    (a b : Fin 2) : Polynomial Complex :=
  ∑ F ∈ evenSubgraphs (triangularTorusGraph L),
    Polynomial.monomial F.card
      ((ons_spinCharacter a b
        (triangularTorusEvenHomology L F) : Complex) *
        ∏ edge ∈ F, weight edge)

end StatMech.FrontierA
