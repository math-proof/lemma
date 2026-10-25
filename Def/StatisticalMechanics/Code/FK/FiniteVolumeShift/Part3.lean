/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteVolumeShift.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.TranslationInvariance.Part5
import Theorem.StatisticalMechanics.Code.FK.FiniteVolumeShift.Part2
open MeasureTheory Filter Topology SimpleGraph Set
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK ConfigSpace


variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]


variable (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]


variable (bdryV : V → Prop) [DecidablePred bdryV] (bdryW : W → Prop) [DecidablePred bdryW]


noncomputable def fvs_wiredGraphIso (σ : V ≃ W)
    (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y)) (hbdry : ∀ x, bdryV x ↔ bdryW (σ x))
    (ω : ConfigSpace (Sym2 W)) :
    StatMech.Lattice.wiredGraph G bdryV (reCfgIso σ ω)
      ≃g StatMech.Lattice.wiredGraph H bdryW ω where
  toEquiv := σ
  map_rel_iff' := by
    intro x y
    simp only [StatMech.Lattice.wiredGraph_adj, reCfgIso]
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
