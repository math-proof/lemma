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
import Instance.StatisticalMechanics.Code.FK.EsCorrelations
open scoped BigOperators

set_option linter.style.show false


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def connProb (p q : ℝ) (x y : V) : ℝ :=
  ∑ ω ∈ Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => Connected G ω x y),
    fkProb G p q ω


noncomputable def eqFunEquiv {C : Type*} [Fintype C] [DecidableEq C] (q : ℕ) (a b : C)
    (hab : a ≠ b) :
    {f : C → Fin q // f a = f b} ≃ ({c : C // c ≠ b} → Fin q) where
  toFun f := fun c => f.1 c.1
  invFun g := ⟨fun c => if h : c = b then g ⟨a, hab⟩ else g ⟨c, h⟩, by
    show (if h : a = b then g ⟨a, hab⟩ else g ⟨a, h⟩)
        = if h : b = b then g ⟨a, hab⟩ else g ⟨b, h⟩
    rw [dif_neg hab, dif_pos rfl]⟩
  left_inv f := by
    apply Subtype.ext
    funext c
    simp only
    by_cases h : c = b
    · rw [dif_pos h, h]; exact f.2
    · rw [dif_neg h]
  right_inv g := by
    funext c
    simp only
    rw [dif_neg c.2]


end FK
end StatMech
