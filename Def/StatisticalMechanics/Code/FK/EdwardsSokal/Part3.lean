/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.Potts.Part6
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokal.Part2
open scoped BigOperators


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def constOnOpenEquiv {q : ℕ} (ω : ConfigSpace (Sym2 V)) :
    ((openSub G ω).ConnectedComponent → Fin q) ≃ {σ : V → Fin q // ConstOnOpen G ω σ} where
  toFun τ := ⟨fun v => τ ((openSub G ω).connectedComponentMk v), by
    intro x y hxy
    simp only
    congr 1
    exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxy⟩
  invFun σ := SimpleGraph.ConnectedComponent.lift σ.1 (by
    intro v w p _
    exact constOnOpen_reachable G ω σ.1 σ.2 p.reachable)
  left_inv τ := by
    funext c
    induction c using SimpleGraph.ConnectedComponent.ind with
    | _ v => rfl
  right_inv σ := by
    apply Subtype.ext
    funext v
    rfl


end FK
end StatMech
