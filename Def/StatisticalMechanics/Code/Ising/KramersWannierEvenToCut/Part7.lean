/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierEvenToCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierGeneral.Part5
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierEvenToCut.Part6
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Ising

section Reduction

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Gp Gd : SimpleGraph V} [DecidableRel Gp.Adj] [DecidableRel Gd.Adj]


section ClosedWalk

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Gp Gd : SimpleGraph V} [DecidableRel Gp.Adj] [DecidableRel Gd.Adj]


def ClosedDualWalkParity (Gp Gd : SimpleGraph V) [DecidableRel Gp.Adj]
    (ψ : Sym2 V ≃ Sym2 V) : Prop :=
  ∀ {w : V} (W : Gd.Walk w w), EvenOnCycles Gp ((W.edges.toFinset).image ψ.symm)


def EvenSubgraphWalkDecomp (Gd : SimpleGraph V) [DecidableRel Gd.Adj] : Prop :=
  ∀ F ∈ evenSubgraphs Gd, ∃ (ι : Type) (_ : DecidableEq ι) (s : Finset ι)
      (w : ι → V) (W : (i : ι) → Gd.Walk (w i) (w i)),
    F = s.biUnion (fun i => (W i).edges.toFinset) ∧
    (s : Set ι).PairwiseDisjoint (fun i => (W i).edges.toFinset)


end ClosedWalk
end Reduction
end Ising
end StatMech
