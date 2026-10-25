/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/PermCycleQuotientCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialRibbonBoundaryParity.Part3
import Def.StatisticalMechanics.Code.FrontierA.PermCycleQuotientCount


namespace StatMech.FrontierA

open Equiv

variable {D : Type*} [Fintype D] [DecidableEq D]


theorem permCycleRepresentativeOf_eq_iff_sameCycle
    (sigma : Perm D) (x y : D) :
    permCycleRepresentativeOf sigma x =
        permCycleRepresentativeOf sigma y ↔
      sigma.SameCycle x y := by
  classical
  by_cases hx : x ∈ sigma.support <;>
    by_cases hy : y ∈ sigma.support
  · simp only [permCycleRepresentativeOf, dif_pos hx, dif_pos hy,
      Sum.inl.injEq, Subtype.ext_iff]
    exact (Equiv.Perm.sameCycle_iff_cycleOf_eq_of_mem_support hx hy).symm
  · simp only [permCycleRepresentativeOf, dif_pos hx, dif_neg hy,
      Sum.inl_ne_inr, false_iff]
    intro hxy
    have hyfix : sigma y = y := by
      simpa only [Equiv.Perm.notMem_support] using hy
    have hxfix : sigma x = x :=
      (hxy.apply_eq_self_iff).2 hyfix
    exact (Equiv.Perm.mem_support.mp hx) hxfix
  · simp only [permCycleRepresentativeOf, dif_neg hx, dif_pos hy,
      Sum.inr_ne_inl, false_iff]
    intro hxy
    have hxfix : sigma x = x := by
      simpa only [Equiv.Perm.notMem_support] using hx
    have hyfix : sigma y = y :=
      (hxy.apply_eq_self_iff).1 hxfix
    exact (Equiv.Perm.mem_support.mp hy) hyfix
  · simp only [permCycleRepresentativeOf, dif_neg hx, dif_neg hy,
      Sum.inr.injEq, Subtype.ext_iff]
    constructor
    · intro hxy
      exact hxy.sameCycle sigma
    · intro hxy
      have hxfix : sigma x = x := by
        simpa only [Equiv.Perm.notMem_support] using hx
      exact hxy.eq_of_left hxfix

theorem permCycleRepresentativeOf_surjective (sigma : Perm D) :
    Function.Surjective (permCycleRepresentativeOf sigma) := by
  classical
  rintro (c | x)
  · obtain ⟨a, ha⟩ :=
      Equiv.Perm.IsCycle.nonempty_support
        (Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.2).1
    refine ⟨a, ?_⟩
    simp only [permCycleRepresentativeOf, dif_pos
      (Equiv.Perm.mem_cycleFactorsFinset_support_le c.2 ha), Sum.inl.injEq,
      Subtype.ext_iff]
    exact (Equiv.Perm.cycle_is_cycleOf ha c.2).symm
  · refine ⟨x.1, ?_⟩
    have hx : x.1 ∉ sigma.support := by
      rw [Equiv.Perm.notMem_support]
      exact x.2
    simp [permCycleRepresentativeOf, hx]


end StatMech.FrontierA
