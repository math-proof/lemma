/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeane.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.Theta
import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Def.StatisticalMechanics.Code.Percolation.BurtonKeane.Part3
open MeasureTheory

set_option linter.style.show false


namespace StatMech

namespace Percolation

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}


lemma image_cluster_repSet (ω : ConfigSpace (Sym2 (Site d))) :
    (fun x => cluster d ω x) '' (repSet d ω) = infiniteClusters d ω := by
  ext C
  simp only [Set.mem_image, repSet, Set.mem_setOf_eq, infiniteClusters]
  constructor
  · rintro ⟨x, ⟨hinf, _⟩, rfl⟩
    exact ⟨hinf, x, rfl⟩
  · rintro ⟨hinf, x, rfl⟩
    obtain ⟨z, hz, hmin⟩ := exists_encode_min (cluster d ω x) ⟨x, self_mem_cluster ω x⟩
    rw [mem_cluster] at hz
    refine ⟨z, ⟨?_, ?_⟩, ?_⟩
    · rwa [← cluster_eq_of_connected hz]
    · intro y hzy
      exact hmin y (by rw [mem_cluster]; exact hz.trans hzy)
    · exact (cluster_eq_of_connected hz).symm


lemma injOn_cluster_repSet (ω : ConfigSpace (Sym2 (Site d))) :
    Set.InjOn (fun x => cluster d ω x) (repSet d ω) := by
  intro a ha b hb hab
  simp only at hab
  have hab' : b ∈ cluster d ω a := by rw [hab]; exact self_mem_cluster ω b
  rw [mem_cluster] at hab'
  have h1 := ha.2 b hab'
  have h2 := hb.2 a hab'.symm
  exact Encodable.encode_injective (le_antisymm h1 h2)


lemma numInfiniteClusters_eq_repSet_encard (ω : ConfigSpace (Sym2 (Site d))) :
    numInfiniteClusters d ω = (repSet d ω).encard := by
  unfold numInfiniteClusters
  rw [← image_cluster_repSet, Set.InjOn.encard_image (injOn_cluster_repSet ω)]


lemma measurableSet_repSet (x : Site d) :
    MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | x ∈ repSet d ω} := by
  classical
  have hpred : MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) |
      ∀ y, Connected d ω x y → Encodable.encode x ≤ Encodable.encode y} := by
    have heq : {ω : ConfigSpace (Sym2 (Site d)) |
          ∀ y, Connected d ω x y → Encodable.encode x ≤ Encodable.encode y}
        = ⋂ y ∈ {y : Site d | Encodable.encode y < Encodable.encode x},
            {ω | ¬ Connected d ω x y} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro h y hy hc; exact absurd (h y hc) (not_le.mpr hy)
      · intro h y hc; by_contra hlt; rw [not_le] at hlt; exact h y hlt hc
    rw [heq]
    apply MeasurableSet.biInter (Set.to_countable _); intro y _
    exact (measurableSet_connected x y).compl
  have : {ω : ConfigSpace (Sym2 (Site d)) | x ∈ repSet d ω}
      = {ω | (cluster d ω x).Infinite}
          ∩ {ω | ∀ y, Connected d ω x y → Encodable.encode x ≤ Encodable.encode y} := by
    ext ω; simp only [repSet, Set.mem_setOf_eq, Set.mem_inter_iff]
  rw [this]
  exact (measurableSet_clusterInfinite x).inter hpred


lemma measurable_encard_setOf {Ω α : Type*} [MeasurableSpace Ω] [Countable α]
    (p : Ω → α → Prop) (hp : ∀ a, Measurable (fun ω => p ω a)) :
    Measurable (fun ω => Set.encard {a | p ω a}) := by
  have h1 : Measurable (fun ω => (fun a => p ω a)) := by
    rw [measurable_pi_iff]; exact hp
  exact measurable_encard.comp (measurable_setOf.comp h1)


theorem measurable_numInfiniteClusters :
    Measurable (numInfiniteClusters d) := by
  have heq : numInfiniteClusters d = fun ω => Set.encard {x : Site d | x ∈ repSet d ω} := by
    funext ω
    rw [numInfiniteClusters_eq_repSet_encard]
    rfl
  rw [heq]
  refine measurable_encard_setOf (fun ω x => x ∈ repSet d ω) (fun x => ?_)
  exact measurable_mem.mpr (measurableSet_repSet x)


theorem numInfiniteClusters_ae_const
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ) :
    ∃ k : ℕ∞, μ {ω | numInfiniteClusters d ω = k} = 1 := by
  refine StatMech.ConfigSpace.ergodic_ae_const_of_shiftInvariant herg
    (numInfiniteClusters d) measurable_numInfiniteClusters ?_
  intro g ω
  exact numInfiniteClusters_shift g ω

end Percolation
end StatMech
