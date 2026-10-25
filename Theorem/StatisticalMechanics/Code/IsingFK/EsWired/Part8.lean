/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/EsWired.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokal.Part7
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.Coloring.Part6
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
import Instance.StatisticalMechanics.Code.IsingFK.EsWired.Part3
open scoped BigOperators


namespace StatMech

namespace IsingFK

open StatMech.FK StatMech.Potts StatMech.Lattice

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


variable (bdry : V → Prop) [DecidablePred bdry]


omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [DecidablePred bdry] in


theorem constOnWired_reachable {q : ℕ} (ω : ConfigSpace (Sym2 V)) (σ : V → Fin q)
    (h : ConstOnWired G bdry ω σ) {x y : V} (r : (wiredSub G bdry ω).Reachable x y) :
    σ x = σ y := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at r
  induction r with
  | refl => rfl
  | tail _ hab ih => rw [ih]; exact h _ _ hab

omit [DecidableRel G.Adj] in


theorem constOnOpen_boundaryFixed_iff {q : ℕ} (b : Fin q) (ω : ConfigSpace (Sym2 V))
    (σ : V → Fin q) :
    (ConstOnOpen G ω σ ∧ BoundaryFixed bdry b σ)
      ↔ (ConstOnWired G bdry ω σ ∧ BoundaryFixed bdry b σ) := by
  constructor
  · rintro ⟨hopen, hbf⟩
    refine ⟨?_, hbf⟩
    intro x y hxy
    rw [wiredSub, SimpleGraph.sup_adj] at hxy
    rcases hxy with hxy | hxy
    · exact hopen x y hxy
    · rw [boundaryCliqueGraph_adj] at hxy
      rw [hbf x hxy.2.1, hbf y hxy.2.2]
  · rintro ⟨hwired, hbf⟩
    refine ⟨?_, hbf⟩
    intro x y hxy
    exact hwired x y (by rw [wiredSub, SimpleGraph.sup_adj]; exact Or.inl hxy)


end IsingFK
end StatMech
