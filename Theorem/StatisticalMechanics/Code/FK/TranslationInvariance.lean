/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationInvariance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.DensityFiniteToInfinite.Part2
import Def.StatisticalMechanics.Code.FK.TranslationInvariance
open MeasureTheory Filter Topology SimpleGraph Set
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK ConfigSpace


variable {V : Type*} [Fintype V] [DecidableEq V]


theorem fkTI_reCfg_apply (σ : V ≃ V) (ω : ConfigSpace (Sym2 V)) (e : Sym2 V) :
    reCfg σ ω e = ω (Sym2.map σ e) := rfl

theorem fkTI_reCfg_reCfg (σ : V ≃ V) (ω : ConfigSpace (Sym2 V)) :
    reCfg σ.symm (reCfg σ ω) = ω := by
  funext e; unfold reCfg; rw [Sym2.map_map]; simp

theorem fkTI_reCfg_reCfg' (σ : V ≃ V) (ω : ConfigSpace (Sym2 V)) :
    reCfg σ (reCfg σ.symm ω) = ω := by
  funext e; unfold reCfg; rw [Sym2.map_map]; simp


end FK
end StatMech
