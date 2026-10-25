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
import Theorem.StatisticalMechanics.Code.IsingFK.EsWired.Part8
open scoped BigOperators


namespace StatMech

namespace IsingFK

open StatMech.FK StatMech.Potts StatMech.Lattice

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


variable (bdry : V → Prop) [DecidablePred bdry]


noncomputable def constOnWiredEquiv {q : ℕ} (ω : ConfigSpace (Sym2 V)) :
    ((wiredSub G bdry ω).ConnectedComponent → Fin q)
      ≃ {σ : V → Fin q // ConstOnWired G bdry ω σ} where
  toFun τ := ⟨fun v => τ ((wiredSub G bdry ω).connectedComponentMk v), by
    intro x y hxy
    simp only
    congr 1
    exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxy⟩
  invFun σ := SimpleGraph.ConnectedComponent.lift σ.1 (by
    intro v w p _
    exact constOnWired_reachable G bdry ω σ.1 σ.2 p.reachable)
  left_inv τ := by
    funext c
    induction c using SimpleGraph.ConnectedComponent.ind with
    | _ v => rfl
  right_inv σ := by
    apply Subtype.ext
    funext v
    rfl

end IsingFK
end StatMech
