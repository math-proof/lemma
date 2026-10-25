/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalFineFiberFactorization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalFineRowProfile.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalFineFiberFactorization.Part4
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexHorizontalFineRowProfileSignedSum_eq_minorConvolution
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (profile : SixVertexHorizontalBoundedFineRowProfile T) :
    sixVertexHorizontalFineRowProfileSignedSum T
        sourceLeft sourceRight targetLeft targetRight profile =
      ∑ first : SixVertexHorizontalBoundedSingleRowProfile T,
        ∑ second : SixVertexHorizontalBoundedSingleRowProfile T,
          if sixVertexHorizontalAddSingleRowProfiles first second = profile then
            (sixVertexHorizontalSingleRowProfileSectorSum
                T targetLeft first : Int) *
                sixVertexHorizontalSingleRowProfileSectorSum
                  T targetRight second -
              (sixVertexHorizontalSingleRowProfileSectorSum
                  T sourceLeft first : Int) *
                sixVertexHorizontalSingleRowProfileSectorSum
                  T sourceRight second
          else 0 := by
  unfold sixVertexHorizontalFineRowProfileSignedSum
  rw [sixVertexHorizontalFineRowProfileSectorPairSum_eq_convolution,
    sixVertexHorizontalFineRowProfileSectorPairSum_eq_convolution,
    Nat.cast_sum, Nat.cast_sum]
  simp_rw [Nat.cast_sum, Nat.cast_ite, Nat.cast_mul, Nat.cast_zero]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro first hfirst
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro second hsecond
  by_cases hprofile :
      sixVertexHorizontalAddSingleRowProfiles first second = profile <;>
    simp [hprofile]


theorem sixVertexHorizontalFineRowProfileSignedSum_eq_kernelSum
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (profile : SixVertexHorizontalBoundedFineRowProfile T) :
    sixVertexHorizontalFineRowProfileSignedSum T
        sourceLeft sourceRight targetLeft targetRight profile =
      ∑ horizontal : SixVertexHorizontalField T ×
          SixVertexHorizontalField T,
        if sixVertexHorizontalPairBoundedFineRowProfile horizontal = profile
        then sixVertexHorizontalProfileSignedKernel
          sourceLeft sourceRight targetLeft targetRight
          (sixVertexHorizontalPairCompletionProfile T horizontal)
        else 0 := by
  unfold sixVertexHorizontalFineRowProfileSignedSum
    sixVertexHorizontalFineRowProfileSectorPairSum
    sixVertexHorizontalProfileSignedKernel
  simp_rw [Nat.cast_sum, Nat.cast_ite, Nat.cast_mul, Nat.cast_zero]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro horizontal hhorizontal
  by_cases hprofile :
      sixVertexHorizontalPairBoundedFineRowProfile horizontal = profile
  · simp only [hprofile, if_true]
    rw [← sixVertexHorizontalPairChooseWeight_eq_profile
        T targetLeft targetRight horizontal,
      ← sixVertexHorizontalPairChooseWeight_eq_profile
        T sourceLeft sourceRight horizontal]
    simp
  · simp [hprofile]

theorem sum_subtype_indicator_eq_sum_indicator_of_imp
    {A : Type*} [Fintype A] (p q : A -> Prop)
    [DecidablePred p] [DecidablePred q]
    (hqp : forall x, q x -> p x) (f : A -> Int) :
    (∑ x : {x : A // p x}, if q x.1 then f x.1 else 0) =
      ∑ x : A, if q x then f x else 0 := by
  classical
  rw [← Finset.sum_subtype
    ((Finset.univ : Finset A).filter p) (by simp) (fun x =>
      if q x then f x else 0), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hq : q x
  · simp [hq, hqp x hq]
  · simp [hq]


theorem fineRowProfileSignedNonnegative_of_raw
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (hraw : forall profile : SixVertexHorizontalBoundedFineRowProfile T,
      0 <= sixVertexHorizontalFineRowProfileSignedSum T
        sourceLeft sourceRight targetLeft targetRight profile) :
    SixVertexHorizontalFineRowProfileAggregateSignedNonnegative T
      sourceLeft sourceRight targetLeft targetRight := by
  intro grade rowProfile profile
  by_cases hgrade :
      grade = sixVertexHorizontalFineRowProfileGrade profile
  · subst grade
    by_cases hrow :
        rowProfile = sixVertexHorizontalFineRowProfileRowZero profile
    · subst rowProfile
      have hrawProfile := hraw profile
      rw [sixVertexHorizontalFineRowProfileSignedSum_eq_kernelSum]
        at hrawProfile
      rw [Finset.sum_filter]
      let p := fun horizontal : SixVertexHorizontalField T ×
          SixVertexHorizontalField T =>
        sixVertexHorizontalPairBigrade horizontal =
            sixVertexHorizontalFineRowProfileGrade profile /\
          sixVertexHorizontalPairRowZeroProfile horizontal =
            sixVertexHorizontalFineRowProfileRowZero profile
      let q := fun horizontal : SixVertexHorizontalField T ×
          SixVertexHorizontalField T =>
        sixVertexHorizontalPairBoundedFineRowProfile horizontal = profile
      let f := fun horizontal : SixVertexHorizontalField T ×
          SixVertexHorizontalField T =>
        sixVertexHorizontalProfileSignedKernel
          sourceLeft sourceRight targetLeft targetRight
          (sixVertexHorizontalPairCompletionProfile T horizontal)
      have hqp : forall horizontal, q horizontal -> p horizontal := by
        intro horizontal hfine
        constructor
        · rw [sixVertexHorizontalPairBigrade_eq_fineRowProfileGrade,
            hfine]
        · rw [sixVertexHorizontalPairRowZeroProfile_eq_fineRowProfileRowZero,
            hfine]
      change 0 <= ∑ horizontal : {horizontal // p horizontal},
        if q horizontal.1 then f horizontal.1 else 0
      rw [sum_subtype_indicator_eq_sum_indicator_of_imp p q hqp f]
      exact hrawProfile
    · have hsum :
          (∑ horizontal ∈
            (Finset.univ : Finset
              (SixVertexHorizontalPairRowBigradeFiber T
                (sixVertexHorizontalFineRowProfileGrade profile)
                rowProfile)).filter
              (fun horizontal =>
                sixVertexHorizontalPairBoundedFineRowProfile horizontal.1 =
                  profile),
            sixVertexHorizontalProfileSignedKernel
              sourceLeft sourceRight targetLeft targetRight
              (sixVertexHorizontalPairCompletionProfile T horizontal.1)) = 0 := by
        apply Finset.sum_eq_zero
        intro horizontal hhorizontal
        have hfine := (Finset.mem_filter.mp hhorizontal).2
        have hforced :=
          sixVertexHorizontalPairRowZeroProfile_eq_fineRowProfileRowZero
            horizontal.1
        rw [hfine] at hforced
        exact False.elim (hrow (horizontal.2.2.symm.trans hforced))
      rw [hsum]
  · have hsum :
        (∑ horizontal ∈
          (Finset.univ : Finset
            (SixVertexHorizontalPairRowBigradeFiber T grade
              rowProfile)).filter
            (fun horizontal =>
              sixVertexHorizontalPairBoundedFineRowProfile horizontal.1 =
                profile),
          sixVertexHorizontalProfileSignedKernel
            sourceLeft sourceRight targetLeft targetRight
            (sixVertexHorizontalPairCompletionProfile T horizontal.1)) = 0 := by
      apply Finset.sum_eq_zero
      intro horizontal hhorizontal
      have hfine := (Finset.mem_filter.mp hhorizontal).2
      have hforced :=
        sixVertexHorizontalPairBigrade_eq_fineRowProfileGrade horizontal.1
      rw [hfine] at hforced
      exact False.elim (hgrade (horizontal.2.1.symm.trans hforced))
    rw [hsum]


theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_rawFineProfile
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hraw : forall profile : SixVertexHorizontalBoundedFineRowProfile T,
      0 <= sixVertexHorizontalFineRowProfileSignedSum T
        ⟨middle.val - 1, by omega⟩ ⟨middle.val + 1, by omega⟩
        middle middle profile) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val :=
  sixVertexMarkedTraceCoefficientwiseLogConcave_of_fineRowProfileSigned
    T middle hmiddle_pos hmiddle_lt
      (fineRowProfileSignedNonnegative_of_raw T
        ⟨middle.val - 1, by omega⟩ ⟨middle.val + 1, by omega⟩
        middle middle hraw)

end
end StatMech.FrontierD
