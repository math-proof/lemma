/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainHomology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainEvenPolynomial.Part11
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardTwist.Part7
open scoped BigOperators


namespace StatMech.FrontierA

open Finset SimpleGraph

noncomputable section

def kwOrderedSplitEdgeClass
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (edgeClass : Sym2 V → SurfaceHomology 1) :
    Sym2 (KWDartPort G) → SurfaceHomology 1 :=
  fun edge => edgeClass (kwOrderedSplitEdgeProjection edge)

end
end StatMech.FrontierA
