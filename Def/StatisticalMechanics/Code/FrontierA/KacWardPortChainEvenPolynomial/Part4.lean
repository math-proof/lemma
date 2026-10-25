/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part32
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStar.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainEvenPolynomial.Part3
open scoped BigOperators


namespace StatMech.FrontierA

open Finset SimpleGraph

open StatMech.Ising


def kwNeighborEquivOutgoingDart
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    G.neighborSet v ≃ KWOutgoingDart (G := G) v where
  toFun w := ⟨⟨(v, w.1), w.2⟩, rfl⟩
  invFun d := ⟨d.1.snd, by
    change G.Adj v d.1.snd
    simpa [d.2] using d.1.adj⟩
  left_inv w := by
    apply Subtype.ext
    rfl
  right_inv d := by
    apply Subtype.ext
    apply SimpleGraph.Dart.ext
    exact Prod.ext d.2.symm rfl

end StatMech.FrontierA
