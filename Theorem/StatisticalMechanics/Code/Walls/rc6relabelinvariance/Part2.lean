/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6relabelinvariance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc6deficitform.Part4
import Theorem.StatisticalMechanics.Code.Walls.rc5_reindextransfer
import Def.StatisticalMechanics.Code.Walls.rc6relabelinvariance
open Finset
open scoped StatMech


namespace StatMech.Walls

open StatMech ConfigSpace


theorem rc6_deficitNonposAllFinite_iff :
    rc6_DeficitNonposAllFinite ↔ rc6_DeficitNonpos := by
  unfold rc6_DeficitNonposAllFinite rc6_DeficitNonpos
  constructor
  · intro h n A B; exact h (Fin n) A B
  · intro h β _ _ A B; exact rc6_deficitNonpos_of_fin h A B


theorem rc6_reimerCardFormAll_iff_deficitNonposAllFinite :
    ReimerCardFormAll ↔ rc6_DeficitNonposAllFinite := by
  rw [rc6_deficitNonposAllFinite_iff, ← rc6_deficitNonpos_iff_reimerCardFormAll]


theorem rc6_reimerCardForm_of_reimerCardFormAll (hcard : ReimerCardFormAll)
    {β : Type*} [Fintype β] [DecidableEq β] (A B : Set (ConfigSpace β)) :
    StatMech.poc_ReimerCardForm A B := by
  rw [rc6_reimerCardForm_iff_deficit]
  exact rc6_deficitNonpos_of_fin (rc6_deficitNonpos_iff_reimerCardFormAll.mpr hcard) A B


theorem rc6_relabel_invariance :
    (∀ {E F : Type} [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]
        (e : E ≃ F) (A B : Set (ConfigSpace E)),
        rc6_deficit A B = rc6_deficit (cfgEquiv e ⁻¹' A) (cfgEquiv e ⁻¹' B))
      ∧ (rc6_DeficitNonposAllFinite ↔ rc6_DeficitNonpos)
      ∧ (ReimerCardFormAll ↔ rc6_DeficitNonposAllFinite) :=
  ⟨fun e A B => rc6_deficit_cfgEquiv_invariant e A B,
    rc6_deficitNonposAllFinite_iff,
    rc6_reimerCardFormAll_iff_deficitNonposAllFinite⟩

end StatMech.Walls
