/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part32
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStar.Part4
import Def.StatisticalMechanics.Code.FrontierA.KacWardPortChainEvenPolynomial.Part7
open scoped BigOperators


namespace StatMech.FrontierA

open Finset SimpleGraph

open StatMech.Ising


@[simp] theorem kwOrderedSplitEdgeBitValue_edge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G) (b : KWDartEdgeBits G)
    (y : KWPortChainField G)
    (d : (kwOrderedDartPortSplitGraph G order).Dart) :
    kwOrderedSplitEdgeBitValue G order b y d.edge =
      kwOrderedPortSplitAdjBit G order b y d.fst d.snd := by
  rcases d with ⟨⟨p, q⟩, hpq⟩
  change (if h : (kwOrderedDartPortSplitGraph G order).Adj p q then
      kwOrderedPortSplitAdjBit G order b y p q else 0) = _
  rw [dif_pos hpq]


end StatMech.FrontierA
