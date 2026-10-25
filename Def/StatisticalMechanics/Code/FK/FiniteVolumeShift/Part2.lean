/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteVolumeShift.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.TranslationInvariance.Part5
import Theorem.StatisticalMechanics.Code.FK.FiniteVolumeShift
open MeasureTheory Filter Topology SimpleGraph Set
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK ConfigSpace


variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]


noncomputable def reCfgIsoEquiv (σ : V ≃ W) :
    ConfigSpace (Sym2 W) ≃ ConfigSpace (Sym2 V) where
  toFun := reCfgIso σ
  invFun := reCfgIso σ.symm
  left_inv := fvs_reCfgIso_reCfgIso σ
  right_inv := fvs_reCfgIso_reCfgIso' σ


variable (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]


noncomputable def fvs_openSubIso (σ : V ≃ W)
    (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y)) (ω : ConfigSpace (Sym2 W)) :
    openSub G (reCfgIso σ ω) ≃g openSub H ω where
  toEquiv := σ
  map_rel_iff' := by
    intro x y
    simp only [openSub_adj, reCfgIso]
    rw [Sym2.map_mk, hσ x y]


end FK
end StatMech
