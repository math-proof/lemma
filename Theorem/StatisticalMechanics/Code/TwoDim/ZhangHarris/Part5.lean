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
import Def.StatisticalMechanics.Code.TwoDim.ZhangHarris.Part5
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal


namespace StatMech.TwoDim

open StatMech.Lattice StatMech.Percolation StatMech.Universality

open StatMech.RSW.Box

theorem zih_RightArmApprox_dependsOn (k N m : ℕ) :
    StatMech.DependsOn (zih_RightArmApprox k N m)
      (zih_rightApproxSupport k N m) := by
  apply ih_dependsOn_iUnion
  intro y
  apply ih_dependsOn_inter
  · apply (zih_clusterApprox_dependsOn (y : Site 2) m).mono
    intro e he
    rw [Finset.mem_coe, zih_rightApproxSupport, Finset.mem_union]
    exact Or.inr (Finset.mem_biUnion.mpr ⟨y, y.2, he⟩)
  · apply (zih_rightArmFrom_dependsOn (y : Site 2) N).mono
    intro e he
    rw [Finset.mem_coe, zih_rightApproxSupport, Finset.mem_union]
    exact Or.inl he

theorem zih_RightArmApprox_isIncreasing (k N m : ℕ) :
    IsIncreasing (zih_RightArmApprox k N m) := by
  intro omega omega' hle
  simp only [zih_RightArmApprox, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
  rintro ⟨y, hy, harm⟩
  rcases harm with ⟨hyS, b, hyb⟩
  exact ⟨y, zih_clusterApprox_isIncreasing y m hle hy, hyS, b,
    StatMech.TwoDim.connectedWithin_mono hle hyb⟩

theorem zih_RightArmApprox_measurableSet (k N m : ℕ) :
    MeasurableSet (zih_RightArmApprox k N m) :=
  measurableSet_of_dependsOn
    (ih_indicator_dependsOn_of_event (zih_RightArmApprox_dependsOn k N m))

theorem zih_RightArmApprox_antitone (k N : ℕ) :
    Antitone (zih_RightArmApprox k N) := by
  intro m n hmn omega
  simp only [zih_RightArmApprox, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
  rintro ⟨y, hy, harm⟩
  exact ⟨y, zih_clusterApprox_antitone y hmn hy, harm⟩

theorem zih_RightArmEvent_eq_iInter (k N : ℕ) :
    zfk_RightArmEvent k N = ⋂ m : ℕ, zih_RightArmApprox k N m := by
  change zfk_RightArmEvent k N = ⋂ m : ℕ, ⋃ y : zfk_rightCentralFinset k,
    zih_clusterApprox (y : Site 2) m ∩ {omega | zfk_RightArmFrom omega y N}
  rw [iInter_iUnion_of_antitone]
  · ext omega
    simp only [zfk_RightArmEvent, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter,
      Set.mem_inter_iff]
    constructor
    · rintro ⟨y, hyK, hyInf, harm⟩
      let yf : zfk_rightCentralFinset k :=
        ⟨y, zfk_mem_rightCentralFinset.mpr hyK⟩
      refine ⟨yf, ?_⟩
      have hyi : omega ∈ ⋂ m, zih_clusterApprox y m :=
        (Set.ext_iff.mp (zih_clusterInfinite_eq_iInter y) omega).mp hyInf
      have hyi' : ∀ m, omega ∈ zih_clusterApprox y m := by
        simpa only [Set.mem_iInter] using hyi
      intro m
      exact ⟨hyi' m, harm⟩
    · rintro ⟨y, hy⟩
      have hca : (cluster 2 omega (y : Site 2)).Infinite := by
        exact (Set.ext_iff.mp (zih_clusterInfinite_eq_iInter (y : Site 2)) omega).mpr
          (by simpa only [Set.mem_iInter] using (fun m => (hy m).1))
      exact ⟨y, zfk_mem_rightCentralFinset.mp y.2, hca, (hy 0).2⟩
  · intro y
    exact fun m n hmn => inter_subset_inter (zih_clusterApprox_antitone y hmn)
      Subset.rfl

theorem zih_armPair_fkg (k N : ℕ) :
    halfMeasure.real (zfk_LeftArmEvent k N) *
        halfMeasure.real (zfk_RightArmEvent k N) ≤
      halfMeasure.real (zfk_ArmPairEvent k N) := by
  let F : ℕ → Finset (Sym2 (Site 2)) := fun m =>
    zih_leftApproxSupport k N m ∪ zih_rightApproxSupport k N m
  have hstage : ∀ m,
      halfMeasure.real (zih_LeftArmApprox k N m) *
          halfMeasure.real (zih_RightArmApprox k N m) ≤
        halfMeasure.real
          (zih_LeftArmApprox k N m ∩ zih_RightArmApprox k N m) := by
    intro m
    apply ih_harris_of_finite_dependsOn half_le_one (F m)
    · apply (zih_LeftArmApprox_dependsOn k N m).mono
      intro e he
      exact Finset.mem_union_left _ he
    · apply (zih_RightArmApprox_dependsOn k N m).mono
      intro e he
      exact Finset.mem_union_right _ he
    · exact zih_LeftArmApprox_isIncreasing k N m
    · exact zih_RightArmApprox_isIncreasing k N m
  have hlim := ih_harris_iInter_of_antitone halfMeasure
    (zih_LeftArmApprox k N) (zih_RightArmApprox k N)
    (zih_LeftArmApprox_antitone k N) (zih_RightArmApprox_antitone k N)
    (zih_LeftArmApprox_measurableSet k N) (zih_RightArmApprox_measurableSet k N)
    hstage
  rw [← zih_LeftArmEvent_eq_iInter, ← zih_RightArmEvent_eq_iInter,
    ← zfk_armPair_eq_inter] at hlim
  exact hlim

end StatMech.TwoDim
