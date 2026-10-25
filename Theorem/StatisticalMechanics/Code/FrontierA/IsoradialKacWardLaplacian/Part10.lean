/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialCellularRibbonDuality.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsoradialKacWardLaplacian.Part11


namespace StatMech.FrontierA

open Matrix Finset

open scoped BigOperators

variable {V E D : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype D] [DecidableEq D]


namespace finiteCRSFCycleSupport

theorem mem_toAtomicCycles_support_subset {next : V -> V}
    (S : finiteCRSFCycleSupport next) {cycle : finiteCRSFAtomicCycle next}
    (hcycle : cycle ∈ S.toAtomicCycles) :
    cycle.1.support ⊆ S.carrier := by
  rw [toAtomicCycles, Finset.mem_map] at hcycle
  rcases hcycle with ⟨cycle', _huniv, rfl⟩
  intro v hv
  change v ∈ (Equiv.Perm.ofSubtype cycle'.1).support at hv
  rw [Equiv.Perm.support_ofSubtype] at hv
  rcases Finset.mem_map.mp hv with ⟨w, _hw, rfl⟩
  exact w.property

theorem mem_toAtomicCycles_iff_support_subset {next : V -> V}
    (S : finiteCRSFCycleSupport next) (cycle : finiteCRSFAtomicCycle next) :
    cycle ∈ S.toAtomicCycles ↔ cycle.1.support ⊆ S.carrier := by
  constructor
  · exact S.mem_toAtomicCycles_support_subset
  · intro hsubset
    have hinvariant (v : V) :
        cycle.1 v ∈ S.carrier ↔ v ∈ S.carrier := by
      constructor
      · intro hv
        by_cases hfixed : cycle.1 v = v
        · simpa [hfixed] using hv
        · exact hsubset (Equiv.Perm.mem_support.mpr hfixed)
      · intro hv
        by_cases hfixed : cycle.1 v = v
        · simpa [hfixed] using hv
        · rw [cycle.2.2 v (Equiv.Perm.mem_support.mpr hfixed)]
          exact S.mapsTo v hv
    let restricted : Equiv.Perm (↑S.carrier) :=
      cycle.1.subtypePerm hinvariant
    have hrestrictedCycle : restricted.IsCycle := by
      obtain ⟨v, hv⟩ := cycle.2.1.nonempty_support
      let w : ↑S.carrier := ⟨v, hsubset hv⟩
      refine ⟨w, ?_, ?_⟩
      · intro hfixed
        apply Equiv.Perm.mem_support.mp hv
        have hval := congrArg Subtype.val hfixed
        simpa [restricted, w] using hval
      · intro w' hw'
        have hwAmbient : cycle.1 (w' : V) ≠ w' := by
          intro hfixed
          apply hw'
          apply Subtype.ext
          exact hfixed
        exact (cycle.2.1.sameCycle
          (Equiv.Perm.mem_support.mp hv) hwAmbient).subtypePerm
    have hfactor : restricted ∈ S.atomicCycles := by
      rw [atomicCycles, Equiv.Perm.mem_cycleFactorsFinset_iff]
      refine ⟨hrestrictedCycle, ?_⟩
      intro v hv
      apply Subtype.ext
      have hvAmbient : (v : V) ∈ cycle.1.support := by
        rw [Equiv.Perm.mem_support]
        intro hfixed
        apply Equiv.Perm.mem_support.mp hv
        apply Subtype.ext
        exact hfixed
      calc
        (restricted v : V) = cycle.1 v := rfl
        _ = next v := cycle.2.2 v hvAmbient
        _ = (S.restrictedPerm v : V) := rfl
    rw [toAtomicCycles, Finset.mem_map]
    refine ⟨⟨restricted, hfactor⟩, Finset.mem_univ _, ?_⟩
    apply Subtype.ext
    change Equiv.Perm.ofSubtype restricted = cycle.1
    exact Equiv.Perm.ofSubtype_subtypePerm hinvariant
      (fun v hv => hsubset (Equiv.Perm.mem_support.mpr hv))

theorem carrier_ofAtomicCycles_toAtomicCycles {next : V -> V}
    (S : finiteCRSFCycleSupport next) :
    (ofAtomicCycles S.toAtomicCycles).carrier = S.carrier := by
  ext v
  constructor
  · intro hv
    change v ∈ S.toAtomicCycles.biUnion
      (fun cycle => cycle.1.support) at hv
    rw [Finset.mem_biUnion] at hv
    rcases hv with ⟨cycle, hcycle, hv⟩
    exact S.mem_toAtomicCycles_support_subset hcycle hv
  · intro hv
    obtain ⟨cycle, hcycle, hvcycle⟩ :=
      S.exists_mem_atomicCycle ⟨v, hv⟩
    change v ∈ S.toAtomicCycles.biUnion
      (fun cycle => cycle.1.support)
    rw [Finset.mem_biUnion]
    refine ⟨S.toAtomicCycle ⟨cycle, hcycle⟩, ?_, ?_⟩
    · rw [toAtomicCycles, Finset.mem_map]
      exact ⟨⟨cycle, hcycle⟩, Finset.mem_univ _, rfl⟩
    · change v ∈ (Equiv.Perm.ofSubtype cycle).support
      rw [Equiv.Perm.mem_support,
        Equiv.Perm.ofSubtype_apply_of_mem _ hv]
      intro hfixed
      exact (Equiv.Perm.mem_support.mp hvcycle) (Subtype.ext hfixed)

theorem ofAtomicCycles_toAtomicCycles {next : V -> V}
    (S : finiteCRSFCycleSupport next) :
    ofAtomicCycles S.toAtomicCycles = S := by
  apply finiteCRSFCycleSupport.ext
  exact S.carrier_ofAtomicCycles_toAtomicCycles

theorem toAtomicCycles_ofAtomicCycles {next : V -> V}
    (selected : Finset (finiteCRSFAtomicCycle next)) :
    (ofAtomicCycles selected).toAtomicCycles = selected := by
  ext cycle
  rw [mem_toAtomicCycles_iff_support_subset]
  constructor
  · intro hsubset
    obtain ⟨v, hv⟩ := cycle.2.1.nonempty_support
    have hvUnion := hsubset hv
    change v ∈ selected.biUnion (fun cycle => cycle.1.support) at hvUnion
    rw [Finset.mem_biUnion] at hvUnion
    rcases hvUnion with ⟨cycle', hcycle', hv'⟩
    have hcycles : cycle = cycle' := by
      by_contra hne
      exact (Finset.disjoint_left.mp
        (finiteCRSFAtomicCycle_support_disjoint hne) hv) hv'
    simpa [hcycles] using hcycle'
  · intro hcycle v hv
    change v ∈ selected.biUnion (fun cycle => cycle.1.support)
    rw [Finset.mem_biUnion]
    exact ⟨cycle, hcycle, hv⟩


end finiteCRSFCycleSupport
end StatMech.FrontierA
