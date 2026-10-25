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
import Def.StatisticalMechanics.Code.IsingFK.Coloring.Part4
open scoped BigOperators


namespace StatMech

namespace IsingFK

open StatMech.FK StatMech.Potts

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in

@[simp]
theorem coloring_apply {q : ℕ} (ω : ConfigSpace (Sym2 V))
    (τ : (openSub G ω).ConnectedComponent → Fin q) (x : V) :
    coloring G ω τ x = τ ((openSub G ω).connectedComponentMk x) := rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in


theorem coloring_compatible {q : ℕ} (ω : ConfigSpace (Sym2 V))
    (τ : (openSub G ω).ConnectedComponent → Fin q) :
    Compatible G (coloring G ω τ) ω := by
  rw [compatible_iff_constOnOpen]
  intro x y hxy
  simp only [coloring_apply]
  congr 1
  exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxy

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in


theorem coloring_eq_constOnOpenEquiv {q : ℕ} (ω : ConfigSpace (Sym2 V))
    (τ : (openSub G ω).ConnectedComponent → Fin q) :
    coloring G ω τ = (constOnOpenEquiv G ω τ).1 := rfl


theorem card_compatible {q : ℕ} (ω : ConfigSpace (Sym2 V)) :
    Nat.card {σ : V → Fin q // Compatible G σ ω} = q ^ numClusters G ω := by
  have hcongr : Nat.card {σ : V → Fin q // Compatible G σ ω}
      = Nat.card {σ : V → Fin q // ConstOnOpen G ω σ} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun σ => compatible_iff_constOnOpen G σ ω)
  rw [hcongr, card_constOnOpen]


end IsingFK
end StatMech
