/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part32
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStar.Part4
import Def.StatisticalMechanics.Code.FrontierA.KacWardPortChainEvenPolynomial
open scoped BigOperators


namespace StatMech.FrontierA

open Finset SimpleGraph

open StatMech.Ising


@[simp] theorem kwDartEdgeBitValue_edge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : KWDartEdgeBits G) (d : G.Dart) :
    kwDartEdgeBitValue G b d.edge = b.1 d := by
  rcases d with ⟨⟨v, w⟩, hvw⟩
  simp [kwDartEdgeBitValue, SimpleGraph.Dart.edge, hvw]


end StatMech.FrontierA
