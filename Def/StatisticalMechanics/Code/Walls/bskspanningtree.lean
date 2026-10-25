/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bskspanningtree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bctconnectedtree.Part3
import Theorem.StatisticalMechanics.Code.Walls.bskspanningtree
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


def bsk_augRel {V Leaf : Type*} (H : SimpleGraph V) (par : Leaf → V) :
    (V ⊕ Leaf) → (V ⊕ Leaf) → Prop
  | Sum.inl a, Sum.inl b => H.Adj a b
  | Sum.inl a, Sum.inr l => par l = a
  | Sum.inr l, Sum.inl a => par l = a
  | Sum.inr _, Sum.inr _ => False


def bsk_augG {V Leaf : Type*} (H : SimpleGraph V) (par : Leaf → V) : SimpleGraph (V ⊕ Leaf) :=
  SimpleGraph.fromRel (bsk_augRel H par)

end StatMech.Walls
