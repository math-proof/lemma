module
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAcyclicElimination.Part3
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStraightLineEmbedding.Part2
public import Mathlib.Data.Finset.Sort
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part28
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open SimpleGraph Finset


noncomputable def kwPortSplitAdjBit
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : KWDartEdgeBits G) (y : KWPortChainField G)
    (p q : KWDartPort G) : Fin 2 :=
  if kwDartOfPort G q = (kwDartOfPort G p).symm then
    kwExternalPortBits G b p
  else if q.2.val + 1 = p.2.val then
    y p.1 p.2.castSucc
  else
    y p.1 p.2.succ

end StatMech.FrontierA
