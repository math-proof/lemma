/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAcyclicElimination.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStraightLineEmbedding.Part2
import Mathlib.Data.Finset.Sort
import Def.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part26
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


theorem kwExternalPortBits_matching
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : KWDartEdgeBits G) (p : KWDartPort G) :
    kwExternalPortBits G b (kwPortOfDart G (kwDartOfPort G p).symm) =
      kwExternalPortBits G b p := by
  simp only [kwExternalPortBits, kwDartOfPort_portOfDart]
  exact b.2 _


end StatMech.FrontierA
