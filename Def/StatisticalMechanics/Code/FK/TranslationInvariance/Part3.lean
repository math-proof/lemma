/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationInvariance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.DensityFiniteToInfinite.Part2
import Theorem.StatisticalMechanics.Code.FK.TranslationInvariance.Part2
open MeasureTheory Filter Topology SimpleGraph Set
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK ConfigSpace


variable {V : Type*} [Fintype V] [DecidableEq V]


variable (G : SimpleGraph V) [DecidableRel G.Adj]


variable (bdry : V → Prop) [DecidablePred bdry]


noncomputable def fkTI_wiredGraphIso (σ : V ≃ V)
    (hσ : ∀ x y, G.Adj (σ x) (σ y) ↔ G.Adj x y) (hbdry : ∀ x, bdry (σ x) ↔ bdry x)
    (ω : ConfigSpace (Sym2 V)) :
    StatMech.Lattice.wiredGraph G bdry (reCfg σ ω) ≃g StatMech.Lattice.wiredGraph G bdry ω where
  toEquiv := σ
  map_rel_iff' := by
    intro x y
    simp only [StatMech.Lattice.wiredGraph_adj, reCfg]
    rw [Sym2.map_mk, hσ x y, hbdry x, hbdry y]
    constructor
    · rintro (h | ⟨hne, hx, hy⟩)
      · exact Or.inl h
      · exact Or.inr ⟨fun h => hne (by rw [h]), hx, hy⟩
    · rintro (h | ⟨hne, hx, hy⟩)
      · exact Or.inl h
      · exact Or.inr ⟨fun h => hne (σ.injective h), hx, hy⟩


end FK
end StatMech
