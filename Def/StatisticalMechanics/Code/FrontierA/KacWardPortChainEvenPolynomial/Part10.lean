module
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part32
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStar.Part4
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainEvenPolynomial.Part9
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open Finset SimpleGraph

open StatMech.Ising


def KWActualEvenSubgraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :=
  {F : Finset (Sym2 V) // F ∈ evenSubgraphs G}

end StatMech.FrontierA
