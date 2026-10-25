/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialCellularRibbonDuality.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsoradialKacWardLaplacian.Part7


namespace StatMech.FrontierA

open Matrix Finset

open scoped BigOperators

variable {V E D : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype D] [DecidableEq D]


namespace finiteCRSFCycleSupport

theorem ambientPerm_apply_of_mem {next : V -> V}
    (S : finiteCRSFCycleSupport next) {v : V} (hv : v ∈ S.carrier) :
    S.ambientPerm v = S.restrictedPerm.symm ⟨v, hv⟩ := by
  exact Equiv.Perm.ofSubtype_apply_of_mem _ hv

theorem ambientPerm_apply_of_not_mem {next : V -> V}
    (S : finiteCRSFCycleSupport next) {v : V} (hv : v ∉ S.carrier) :
    S.ambientPerm v = v := by
  exact Equiv.Perm.ofSubtype_apply_of_not_mem _ hv

theorem ambientPerm_symm_apply_of_mem {next : V -> V}
    (S : finiteCRSFCycleSupport next) {v : V} (hv : v ∈ S.carrier) :
    S.ambientPerm.symm v = next v := by
  have hinv : S.ambientPerm.symm =
      Equiv.Perm.ofSubtype S.restrictedPerm := by
    change (Equiv.Perm.ofSubtype S.restrictedPerm.symm)⁻¹ = _
    rw [← map_inv]
    rfl
  rw [hinv, Equiv.Perm.ofSubtype_apply_of_mem _ hv]
  rfl

theorem ambientPerm_ne_of_mem {next : V -> V}
    (S : finiteCRSFCycleSupport next) {v : V} (hv : v ∈ S.carrier) :
    S.ambientPerm v ≠ v := by
  intro hfixed
  have hs : S.ambientPerm.symm v = v := by
    calc
      S.ambientPerm.symm v =
          S.ambientPerm.symm (S.ambientPerm v) :=
        congrArg S.ambientPerm.symm hfixed.symm
      _ = v := S.ambientPerm.symm_apply_apply v
  rw [S.ambientPerm_symm_apply_of_mem hv] at hs
  exact S.noFixed v hv hs


theorem ambientPerm_support {next : V -> V}
    (S : finiteCRSFCycleSupport next) :
    S.ambientPerm.support = S.carrier := by
  ext v
  rw [Equiv.Perm.mem_support]
  constructor
  · intro hmove
    by_contra hv
    exact hmove (S.ambientPerm_apply_of_not_mem hv)
  · exact S.ambientPerm_ne_of_mem


end finiteCRSFCycleSupport
end StatMech.FrontierA
