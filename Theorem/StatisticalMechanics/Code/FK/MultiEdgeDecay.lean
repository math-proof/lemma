/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MultiEdgeDecay.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.CylinderDecayClose.Part6
import Theorem.StatisticalMechanics.Code.FK.OffCentreCarrier
import Def.StatisticalMechanics.Code.FK.MultiEdgeDecay
open MeasureTheory Filter Topology SimpleGraph Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.IsingFK

variable {d : ℕ}


theorem med_boxMultiOpenEvent_eq (N : ℕ) (t : Finset (Sym2 (boxVerts d N))) :
    cdc_boxMultiOpenEvent N t = med_genericMultiOpenEvent t := rfl


theorem med_genericMultiOpenEvent_increasing {V : Type*} (t : Finset (Sym2 V)) :
    IsIncreasing (med_genericMultiOpenEvent t) := by
  intro a b hab ha e he
  have hle := hab e
  rw [ha e he] at hle
  exact le_antisymm (by simp) hle


theorem med_reCfgIso_preimage {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W]
    [DecidableEq W] (σ : V ≃ W) (t : Finset (Sym2 V)) :
    reCfgIso σ ⁻¹' (med_genericMultiOpenEvent t)
      = med_genericMultiOpenEvent (t.image (Sym2.map σ)) := by
  ext ω
  simp only [Set.mem_preimage, med_genericMultiOpenEvent, Set.mem_setOf_eq, reCfgIso,
    Finset.forall_mem_image]

end FK
end StatMech
