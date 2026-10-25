/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialCellularRibbonDuality.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardLaplacian.Part5


namespace StatMech.FrontierA

open Matrix Finset

open scoped BigOperators

variable {V E D : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype D] [DecidableEq D]


namespace finiteCRSFCycleSupport

noncomputable def ofAtomicCycles {next : V -> V}
    (selected : Finset (finiteCRSFAtomicCycle next)) :
    finiteCRSFCycleSupport next where
  carrier := selected.biUnion fun cycle => cycle.1.support
  mapsTo := by
    intro v hv
    rw [Finset.mem_biUnion] at hv ⊢
    rcases hv with ⟨cycle, hcycle, hv⟩
    refine ⟨cycle, hcycle, ?_⟩
    rw [← cycle.2.2 v hv]
    exact Equiv.Perm.apply_mem_support.mpr hv
  injOn := by
    intro a ha b hb hab
    change a ∈ selected.biUnion (fun cycle => cycle.1.support) at ha
    change b ∈ selected.biUnion (fun cycle => cycle.1.support) at hb
    rw [Finset.mem_biUnion] at ha hb
    rcases ha with ⟨cycle, hcycle, ha⟩
    rcases hb with ⟨cycle', hcycle', hb⟩
    have hca : cycle.1 a = next a := cycle.2.2 a ha
    have hcb : cycle'.1 b = next b := cycle'.2.2 b hb
    have hnexta : next a ∈ cycle.1.support := by
      rw [← hca]
      exact Equiv.Perm.apply_mem_support.mpr ha
    have hnextb : next b ∈ cycle'.1.support := by
      rw [← hcb]
      exact Equiv.Perm.apply_mem_support.mpr hb
    have hcycles : cycle = cycle' := by
      by_contra hne
      have hdisjoint := finiteCRSFAtomicCycle_support_disjoint hne
      exact (Finset.disjoint_left.mp hdisjoint hnexta) (by
        rw [hab]
        exact hnextb)
    subst cycle'
    apply cycle.1.injective
    rw [hca, hcb, hab]
  noFixed := by
    intro v hv
    rw [Finset.mem_biUnion] at hv
    rcases hv with ⟨cycle, _hcycle, hv⟩
    intro hnext
    exact (Equiv.Perm.mem_support.mp hv)
      ((cycle.2.2 v hv).trans hnext)


noncomputable def restrictedPerm {next : V -> V}
    (S : finiteCRSFCycleSupport next) : Equiv.Perm (↑S.carrier) := by
  let f : ↑S.carrier -> ↑S.carrier :=
    fun v => ⟨next v, S.mapsTo v v.property⟩
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact S.injOn a.property b.property (congrArg Subtype.val hab)
  exact Equiv.ofBijective f
    ⟨hinj, (Finite.injective_iff_surjective.mp hinj)⟩


noncomputable def ambientPerm {next : V -> V}
    (S : finiteCRSFCycleSupport next) : Equiv.Perm V :=
  Equiv.Perm.ofSubtype S.restrictedPerm.symm

end finiteCRSFCycleSupport
end StatMech.FrontierA
