/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteVolumeShift.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.TranslationInvariance.Part5
import Def.StatisticalMechanics.Code.FK.FiniteVolumeShift
open MeasureTheory Filter Topology SimpleGraph Set
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK ConfigSpace


variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]


theorem fvs_reCfgIso_apply (σ : V ≃ W) (ω : ConfigSpace (Sym2 W)) (e : Sym2 V) :
    reCfgIso σ ω e = ω (Sym2.map σ e) := rfl

theorem fvs_reCfgIso_reCfgIso (σ : V ≃ W) (ω : ConfigSpace (Sym2 W)) :
    reCfgIso σ.symm (reCfgIso σ ω) = ω := by
  funext e; unfold reCfgIso; rw [Sym2.map_map]; simp

theorem fvs_reCfgIso_reCfgIso' (σ : V ≃ W) (ω : ConfigSpace (Sym2 V)) :
    reCfgIso σ (reCfgIso σ.symm ω) = ω := by
  funext e; unfold reCfgIso; rw [Sym2.map_map]; simp


end FK
end StatMech
