/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusCurrentSingletonMixing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.PlusParityPatternMixing.Part2
open MeasureTheory Set
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising Lattice

def mergeLocalPattern {E A : Type*} [DecidableEq E]
    (S T : Finset E) (hdisj : Disjoint S T)
    (a : ↑S -> A) (b : ↑T -> A) : ↑(S ∪ T) -> A :=
  fun i => if hi : i.1 ∈ S then a ⟨i.1, hi⟩
    else b ⟨i.1, (Finset.mem_union.mp i.2).resolve_left hi⟩

end StatMech.FrontierB
