/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangHarris.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.InfiniteHarris.Part3
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangFixedK.Part12
import Theorem.StatisticalMechanics.Code.Percolation.DctItem2.Part2
import Def.StatisticalMechanics.Code.TwoDim.ZhangHarris.Part3
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal


namespace StatMech.TwoDim

open StatMech.Lattice StatMech.Percolation StatMech.Universality

open StatMech.RSW.Box

theorem zih_LeftArmApprox_dependsOn (k N m : ℕ) :
    StatMech.DependsOn (zih_LeftArmApprox k N m)
      (zih_leftApproxSupport k N m) := by
  apply ih_dependsOn_iUnion
  intro x
  apply ih_dependsOn_inter
  · apply (zih_clusterApprox_dependsOn (x : Site 2) m).mono
    intro e he
    rw [Finset.mem_coe, zih_leftApproxSupport, Finset.mem_union]
    exact Or.inr (Finset.mem_biUnion.mpr ⟨x, x.2, he⟩)
  · apply (zih_leftArmFrom_dependsOn (x : Site 2) N).mono
    intro e he
    rw [Finset.mem_coe, zih_leftApproxSupport, Finset.mem_union]
    exact Or.inl he

theorem zih_LeftArmApprox_isIncreasing (k N m : ℕ) :
    IsIncreasing (zih_LeftArmApprox k N m) := by
  intro omega omega' hle
  simp only [zih_LeftArmApprox, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
  rintro ⟨x, hx, harm⟩
  rcases harm with ⟨hxS, a, hax⟩
  exact ⟨x, zih_clusterApprox_isIncreasing x m hle hx, hxS, a,
    StatMech.TwoDim.connectedWithin_mono hle hax⟩

theorem zih_LeftArmApprox_measurableSet (k N m : ℕ) :
    MeasurableSet (zih_LeftArmApprox k N m) := by
  exact measurableSet_of_dependsOn
    (ih_indicator_dependsOn_of_event (zih_LeftArmApprox_dependsOn k N m))

theorem zih_LeftArmApprox_antitone (k N : ℕ) :
    Antitone (zih_LeftArmApprox k N) := by
  intro m n hmn omega
  simp only [zih_LeftArmApprox, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
  rintro ⟨x, hx, harm⟩
  exact ⟨x, zih_clusterApprox_antitone x hmn hx, harm⟩

theorem zih_LeftArmEvent_eq_iInter (k N : ℕ) :
    zfk_LeftArmEvent k N = ⋂ m : ℕ, zih_LeftArmApprox k N m := by
  change zfk_LeftArmEvent k N = ⋂ m : ℕ, ⋃ x : zfk_leftCentralFinset k,
    zih_clusterApprox (x : Site 2) m ∩ {omega | zfk_LeftArmFrom omega x N}
  rw [iInter_iUnion_of_antitone]
  · ext omega
    simp only [zfk_LeftArmEvent, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter,
      Set.mem_inter_iff]
    constructor
    · rintro ⟨x, hxK, hxInf, harm⟩
      let xf : zfk_leftCentralFinset k := ⟨x, zfk_mem_leftCentralFinset.mpr hxK⟩
      refine ⟨xf, ?_⟩
      have hxi : omega ∈ ⋂ m, zih_clusterApprox x m :=
        (Set.ext_iff.mp (zih_clusterInfinite_eq_iInter x) omega).mp hxInf
      have hxi' : ∀ m, omega ∈ zih_clusterApprox x m := by
        simpa only [Set.mem_iInter] using hxi
      intro m
      exact ⟨hxi' m, harm⟩
    · rintro ⟨x, hx⟩
      have hca : (cluster 2 omega (x : Site 2)).Infinite := by
        exact (Set.ext_iff.mp (zih_clusterInfinite_eq_iInter (x : Site 2)) omega).mpr
          (by simpa only [Set.mem_iInter] using (fun m => (hx m).1))
      exact ⟨x, zfk_mem_leftCentralFinset.mp x.2, hca, (hx 0).2⟩
  · intro x
    exact fun m n hmn => inter_subset_inter (zih_clusterApprox_antitone x hmn)
      Subset.rfl

end StatMech.TwoDim
