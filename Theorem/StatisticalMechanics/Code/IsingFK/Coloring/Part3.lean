/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/Coloring.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokal.Part7
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Def.StatisticalMechanics.Code.IsingFK.Coloring.Part3
open scoped BigOperators


namespace StatMech

namespace IsingFK

open StatMech.FK StatMech.Potts

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


omit [DecidableEq V] in

theorem mem_disagreeEdges {q : ℕ} (σ : V → Fin q) (x y : V) :
    s(x, y) ∈ disagreeEdges G σ ↔ G.Adj x y ∧ σ x ≠ σ y := by
  unfold disagreeEdges
  rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
    Bool.not_eq_true, ← Bool.not_eq_true, monoBool_iff]

omit [DecidableEq V] in


theorem compatible_closed_on_disagree {q : ℕ} (σ : V → Fin q) (ω : ConfigSpace (Sym2 V))
    (h : Compatible G σ ω) {e : Sym2 V} (he : e ∈ disagreeEdges G σ) : ω e = false := by
  induction e with
  | _ x y =>
    rw [mem_disagreeEdges] at he
    by_contra hopen
    rw [Bool.not_eq_false] at hopen
    exact he.2 (h x y he.1 hopen)


end IsingFK
end StatMech
