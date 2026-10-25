/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationInvariance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.DensityFiniteToInfinite.Part2
import Theorem.StatisticalMechanics.Code.FK.TranslationInvariance
open MeasureTheory Filter Topology SimpleGraph Set
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK ConfigSpace


variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def reCfgEquiv (σ : V ≃ V) :
    ConfigSpace (Sym2 V) ≃ ConfigSpace (Sym2 V) where
  toFun := reCfg σ
  invFun := reCfg σ.symm
  left_inv := fkTI_reCfg_reCfg σ
  right_inv := fkTI_reCfg_reCfg' σ


variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def fkTI_openSubIso (σ : V ≃ V)
    (hσ : ∀ x y, G.Adj (σ x) (σ y) ↔ G.Adj x y) (ω : ConfigSpace (Sym2 V)) :
    openSub G (reCfg σ ω) ≃g openSub G ω where
  toEquiv := σ
  map_rel_iff' := by
    intro x y
    simp only [openSub_adj, reCfg]
    rw [Sym2.map_mk, hσ x y]


end FK
end StatMech
