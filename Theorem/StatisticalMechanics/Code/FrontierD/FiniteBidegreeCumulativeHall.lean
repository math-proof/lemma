/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteBidegreeCumulativeHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FiniteCumulativeGradeHall
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairDecoratedHall.Part3
import Instance.StatisticalMechanics.Code.FrontierD.FiniteBidegreeCumulativeHall
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem finiteUpperCumulative_of_bidegree
    {Source Target : Type*} [Fintype Source] [Fintype Target]
    (related : Source → Target → Prop)
    (sourceGrade : Source → Nat) (targetGrade : Target → Nat)
    (degree : Nat) (hdegree : 0 < degree)
    (hforward : ∀ source,
      degree ≤ (Finset.univ.filter (related source)).card)
    (hinverse : ∀ target,
      (Finset.univ.filter fun source => related source target).card ≤ degree)
    (hmonotone : ∀ source target,
      related source target → sourceGrade source ≤ targetGrade target) :
    ∀ grade,
      (Finset.univ.filter fun source => grade ≤ sourceGrade source).card ≤
        (Finset.univ.filter fun target => grade ≤ targetGrade target).card := by
  intro grade
  let sources := Finset.univ.filter fun source => grade ≤ sourceGrade source
  let neighbors := Finset.univ.filter fun target =>
    ∃ source ∈ sources, related source target
  have hhall := finiteRelationHall_of_bidegree related degree hdegree
    hforward hinverse sources
  have hsubset : neighbors ⊆
      Finset.univ.filter fun target => grade ≤ targetGrade target := by
    intro target htarget
    simp only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and] at htarget
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    obtain ⟨source, hsource, hrelated⟩ := htarget
    have hgrade : grade ≤ sourceGrade source := by
      simpa [sources] using hsource
    exact hgrade.trans (hmonotone source target hrelated)
  change sources.card ≤
    (Finset.univ.filter fun target => grade ≤ targetGrade target).card
  exact hhall.trans (Finset.card_le_card hsubset)


theorem finiteUpperCumulative_of_twoBranchCapacity
    {Source Target : Type*} [Fintype Source] [Fintype Target]
    (related : Source → Target → Prop)
    (sourceGrade : Source → Nat) (targetGrade : Target → Nat)
    (hforward : ∀ source,
      2 ≤ (Finset.univ.filter (related source)).card)
    (hinverse : ∀ target,
      (Finset.univ.filter fun source => related source target).card ≤ 2)
    (hmonotone : ∀ source target,
      related source target → sourceGrade source ≤ targetGrade target) :
    ∀ grade,
      (Finset.univ.filter fun source => grade ≤ sourceGrade source).card ≤
        (Finset.univ.filter fun target => grade ≤ targetGrade target).card :=
  finiteUpperCumulative_of_bidegree related sourceGrade targetGrade 2
    (by omega) hforward hinverse hmonotone


theorem exists_injective_gradeMonotone_of_twoBranchCapacity
    {Source Target : Type*} [Fintype Source] [Fintype Target]
    (related : Source → Target → Prop)
    (sourceGrade : Source → Nat) (targetGrade : Target → Nat)
    (hforward : ∀ source,
      2 ≤ (Finset.univ.filter (related source)).card)
    (hinverse : ∀ target,
      (Finset.univ.filter fun source => related source target).card ≤ 2)
    (hmonotone : ∀ source target,
      related source target → sourceGrade source ≤ targetGrade target) :
    ∃ matching : Source → Target,
      Function.Injective matching ∧
        ∀ source, sourceGrade source ≤ targetGrade (matching source) := by
  exact exists_injective_gradeMonotone_of_upperCumulative sourceGrade
    targetGrade (finiteUpperCumulative_of_twoBranchCapacity related sourceGrade
      targetGrade hforward hinverse hmonotone)


end
end StatMech.FrontierD
