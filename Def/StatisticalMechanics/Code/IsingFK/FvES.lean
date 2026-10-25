/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/FvES.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokal.Part7
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.EsCorrelations.Part4
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.IsingFK.Coloring.Part6
import Theorem.StatisticalMechanics.Code.IsingFK.EsWired.Part11
import Theorem.StatisticalMechanics.Code.IsingFK.EsLatticeBridge
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
import Theorem.StatisticalMechanics.Code.IsingFK.FvES
open scoped BigOperators


namespace StatMech

namespace IsingFK

open StatMech.FK StatMech.Potts StatMech.Lattice

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

variable (bdry : V → Prop) [DecidablePred bdry]


noncomputable def wiredColourEquiv {q : ℕ} (b : Fin q) (ω : ConfigSpace (Sym2 V))
    (v₀ : V) (hv₀ : bdry v₀) :
    {σ : V → Fin q // ConstOnWired G bdry ω σ ∧ BoundaryFixed bdry b σ}
      ≃ {τ : (wiredSub G bdry ω).ConnectedComponent → Fin q //
            τ ((wiredSub G bdry ω).connectedComponentMk v₀) = b} := by
  refine (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm.trans ?_
  refine ((constOnWiredEquiv G bdry ω).subtypeEquiv ?_).symm
  intro τ
  show (τ ((wiredSub G bdry ω).connectedComponentMk v₀) = b
        ↔ BoundaryFixed bdry b ((constOnWiredEquiv G bdry ω) τ).1)
  constructor
  · intro h x hx
    show τ ((wiredSub G bdry ω).connectedComponentMk x) = b
    rw [wiredSub_componentMk_eq_of_bdry G bdry hx hv₀]; exact h
  · intro h; have := h v₀ hv₀; simpa [constOnWiredEquiv] using this

end IsingFK
end StatMech
