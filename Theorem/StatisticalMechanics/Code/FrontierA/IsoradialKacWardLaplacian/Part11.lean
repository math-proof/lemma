/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialCellularRibbonDuality.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsoradialKacWardLaplacian.Part12


namespace StatMech.FrontierA

open Matrix Finset

open scoped BigOperators

variable {V E D : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype D] [DecidableEq D]


namespace finiteCRSFCycleSupport

theorem support_toAtomicCycle {next : V -> V}
    (S : finiteCRSFCycleSupport next)
    (cycle : {cycle // cycle ∈ S.atomicCycles}) :
    (S.toAtomicCycle cycle).1.support =
      cycle.1.support.map (Function.Embedding.subtype fun v => v ∈ S.carrier) := by
  change (Equiv.Perm.ofSubtype cycle.1).support = _
  ext v
  constructor
  · intro hv
    have hvcarrier : v ∈ S.carrier := by
      by_contra hcarrier
      exact (Equiv.Perm.mem_support.mp hv)
        (Equiv.Perm.ofSubtype_apply_of_not_mem _ hcarrier)
    rw [Finset.mem_map]
    refine ⟨⟨v, hvcarrier⟩, ?_, rfl⟩
    rw [Equiv.Perm.mem_support]
    intro hfixed
    apply Equiv.Perm.mem_support.mp hv
    rw [Equiv.Perm.ofSubtype_apply_of_mem _ hvcarrier]
    exact congrArg Subtype.val hfixed
  · intro hv
    rw [Finset.mem_map] at hv
    rcases hv with ⟨w, hw, rfl⟩
    rw [Equiv.Perm.mem_support]
    change (Equiv.Perm.ofSubtype cycle.1) (w : V) ≠ (w : V)
    rw [Equiv.Perm.ofSubtype_apply_of_mem _ w.property]
    intro hfixed
    exact (Equiv.Perm.mem_support.mp hw) (Subtype.ext hfixed)

theorem holonomy_toAtomicCycle {next : V -> V}
    (transport : V -> V -> Complex) (S : finiteCRSFCycleSupport next)
    (cycle : {cycle // cycle ∈ S.atomicCycles}) :
    (S.toAtomicCycle cycle).holonomy transport =
      S.atomicCycleHolonomy transport cycle.1 := by
  unfold finiteCRSFAtomicCycle.holonomy atomicCycleHolonomy
  change (∏ v ∈ (Equiv.Perm.ofSubtype cycle.1).support,
      transport v (next v)) = _
  have hsupp : (Equiv.Perm.ofSubtype cycle.1).support =
      cycle.1.support.map
        (Function.Embedding.subtype fun v => v ∈ S.carrier) :=
    S.support_toAtomicCycle cycle
  rw [hsupp, Finset.prod_map]
  apply Finset.prod_congr rfl
  intro v _
  rfl

theorem card_toAtomicCycles {next : V -> V}
    (S : finiteCRSFCycleSupport next) :
    S.toAtomicCycles.card = S.atomicCycles.card := by
  simp [toAtomicCycles]

theorem prod_holonomy_toAtomicCycles {next : V -> V}
    (transport : V -> V -> Complex) (S : finiteCRSFCycleSupport next) :
    (∏ cycle ∈ S.toAtomicCycles, cycle.holonomy transport) =
      ∏ cycle ∈ S.atomicCycles,
        S.atomicCycleHolonomy transport cycle := by
  rw [toAtomicCycles, Finset.prod_map]
  calc
    (∏ cycle : {cycle // cycle ∈ S.atomicCycles},
        (S.toAtomicCycle cycle).holonomy transport) =
      ∏ cycle : {cycle // cycle ∈ S.atomicCycles},
        S.atomicCycleHolonomy transport cycle.1 := by
      apply Finset.prod_congr rfl
      intro cycle _
      exact S.holonomy_toAtomicCycle transport cycle
    _ = ∏ cycle ∈ S.atomicCycles,
        S.atomicCycleHolonomy transport cycle := by
      symm
      apply Finset.prod_subtype
      simp


theorem prod_transport_eq_prod_atomicCycleHolonomy {next : V -> V}
    (transport : V -> V -> Complex) (S : finiteCRSFCycleSupport next) :
    (∏ v ∈ S.carrier, transport v (next v)) =
      ∏ cycle ∈ S.atomicCycles,
        S.atomicCycleHolonomy transport cycle := by
  have hunion :
      (Finset.univ : Finset (↑S.carrier)) =
        S.atomicCycles.biUnion fun cycle => cycle.support := by
    ext v
    simp only [Finset.mem_univ, true_iff, Finset.mem_biUnion]
    exact S.exists_mem_atomicCycle v
  have hpairwise :
      Set.PairwiseDisjoint
        (↑S.atomicCycles : Set (Equiv.Perm (↑S.carrier)))
        (fun cycle : Equiv.Perm (↑S.carrier) => cycle.support) := by
    intro cycle hcycle cycle' hcycle' hne
    apply Equiv.Perm.Disjoint.disjoint_support
    exact Equiv.Perm.cycleFactorsFinset_pairwise_disjoint
      S.restrictedPerm hcycle hcycle' hne
  calc
    (∏ v ∈ S.carrier, transport v (next v)) =
        ∏ v : ↑S.carrier, transport v (next v) := by
      apply Finset.prod_subtype
      simp
    _ = ∏ v ∈ (Finset.univ : Finset (↑S.carrier)),
          transport v (next v) := by simp
    _ = ∏ v ∈ (S.atomicCycles.biUnion fun cycle => cycle.support),
          transport v (next v) := by rw [← hunion]
    _ = ∏ cycle ∈ S.atomicCycles,
          ∏ v ∈ cycle.support, transport v (next v) :=
      Finset.prod_biUnion hpairwise
    _ = ∏ cycle ∈ S.atomicCycles,
          S.atomicCycleHolonomy transport cycle := by
      rfl


theorem sign_ambientPerm_eq_atomicCycles {next : V -> V}
    (S : finiteCRSFCycleSupport next) :
    Equiv.Perm.sign S.ambientPerm =
      (-1 : ℤˣ) ^ (S.carrier.card + S.atomicCycles.card) := by
  calc
    Equiv.Perm.sign S.ambientPerm =
        Equiv.Perm.sign S.restrictedPerm.symm := by
      exact Equiv.Perm.sign_ofSubtype S.restrictedPerm.symm
    _ = Equiv.Perm.sign S.restrictedPerm := by
      rw [Equiv.Perm.sign_symm]
    _ = (-1 : ℤˣ) ^ (S.carrier.card + S.atomicCycles.card) := by
      rw [Equiv.Perm.sign_of_cycleType, Equiv.Perm.sum_cycleType,
        S.restrictedPerm_support]
      simp [atomicCycles, Equiv.Perm.cycleType_def]
      rfl

end finiteCRSFCycleSupport
end StatMech.FrontierA
