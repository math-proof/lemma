/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierEvenToCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierGeneral.Part5
import Def.StatisticalMechanics.Code.Ising.KramersWannierEvenToCut.Part8
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


omit [Fintype V] [DecidableEq V] [DecidableRel Gd.Adj] in


theorem edges_eq_nil_of_isEmpty_edgeSet {w : V} (hGd : Gd.edgeSet = ∅)
    (W : Gd.Walk w w) : W.edges = [] := by
  cases W with
  | nil => rfl
  | cons h _ =>
    exact absurd (Gd.mem_edgeSet.mpr h) (by rw [hGd]; exact id)

omit [Fintype V] [DecidableRel Gd.Adj] in


theorem closedDualWalkParity_of_edgeless (ψ : Sym2 V ≃ Sym2 V) (hGd : Gd.edgeSet = ∅) :
    ClosedDualWalkParity Gp Gd ψ := by
  intro w W
  have hnil : W.edges = [] := edges_eq_nil_of_isEmpty_edgeSet hGd W
  have hempty : (W.edges.toFinset).image ψ.symm = (∅ : Finset (Sym2 V)) := by
    rw [hnil]; simp
  rw [hempty]
  exact evenOnCycles_empty Gp

end ClosedWalk
end Reduction
end Ising
end StatMech
