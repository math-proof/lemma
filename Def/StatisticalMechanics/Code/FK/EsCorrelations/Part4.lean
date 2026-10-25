/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EsCorrelations.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokal.Part7
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.EsCorrelations.Part2
open scoped BigOperators

set_option linter.style.show false


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def constEqEquiv {q : ℕ} (ω : ConfigSpace (Sym2 V)) (x y : V) :
    {σ : V → Fin q // ConstOnOpen G ω σ ∧ σ x = σ y} ≃
      {τ : (openSub G ω).ConnectedComponent → Fin q //
        τ ((openSub G ω).connectedComponentMk x)
          = τ ((openSub G ω).connectedComponentMk y)} := by
  refine (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm.trans ?_
  exact ((constOnOpenEquiv G ω).subtypeEquiv (fun _ => Iff.rfl)).symm


end FK
end StatMech
