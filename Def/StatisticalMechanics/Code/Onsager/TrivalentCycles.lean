module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Onsager.CoeffMatch


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TrivalentCycles.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Onsager

open Finset SimpleGraph

open StatMech.Ising

universe u

section

variable {V : Type u} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

def ons_edgeSubgraph (F : Finset (Sym2 V)) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (F : Set (Sym2 V))

end
end StatMech.Onsager
