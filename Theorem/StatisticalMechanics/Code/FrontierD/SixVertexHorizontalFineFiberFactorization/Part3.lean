/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalFineFiberFactorization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalFineRowProfile.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalFineFiberFactorization.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem finite_pair_fiber_factorization
    {A B P Q R S : Type*}
    [Fintype A] [Fintype B] [Fintype P] [Fintype Q]
    [DecidableEq P] [DecidableEq Q] [DecidableEq R]
    [CommSemiring S]
    (leftProfile : A -> P) (rightProfile : B -> Q)
    (combine : P -> Q -> R) (target : R)
    (leftWeight : A -> S) (rightWeight : B -> S) :
    (∑ pair : A × B,
        if combine (leftProfile pair.1) (rightProfile pair.2) = target
        then leftWeight pair.1 * rightWeight pair.2 else 0) =
      ∑ left : P, ∑ right : Q,
        if combine left right = target then
          (∑ a : A, if leftProfile a = left then leftWeight a else 0) *
            (∑ b : B, if rightProfile b = right then rightWeight b else 0)
        else 0 := by
  classical
  let kernel := fun (profile : P × Q) (pair : A × B) =>
    if profile.1 = leftProfile pair.1 then
      if profile.2 = rightProfile pair.2 then
        if combine profile.1 profile.2 = target then
          leftWeight pair.1 * rightWeight pair.2
        else 0
      else 0
    else 0
  have hpoint (pair : A × B) :
      (∑ profile : P × Q, kernel profile pair) =
        if combine (leftProfile pair.1) (rightProfile pair.2) = target
        then leftWeight pair.1 * rightWeight pair.2 else 0 := by
    rw [Fintype.sum_prod_type]
    simp [kernel]
  calc
    _ = ∑ pair : A × B, ∑ profile : P × Q, kernel profile pair := by
      apply Finset.sum_congr rfl
      intro pair hpair
      exact (hpoint pair).symm
    _ = ∑ profile : P × Q, ∑ pair : A × B, kernel profile pair :=
      Finset.sum_comm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro left hleft
      apply Finset.sum_congr rfl
      intro right hright
      by_cases hcombine : combine left right = target
      · simp_rw [kernel, hcombine, if_pos]
        rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
        simp only [eq_comm, ite_mul, mul_ite, zero_mul, mul_zero]
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        by_cases hleftProfile : leftProfile a = left <;>
          by_cases hrightProfile : rightProfile b = right <;>
          simp_all only [eq_comm, if_true, if_false]
      · simp [kernel, hcombine]


theorem sixVertexHorizontalFineRowProfileSectorPairSum_eq_convolution
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (profile : SixVertexHorizontalBoundedFineRowProfile T) :
    sixVertexHorizontalFineRowProfileSectorPairSum T left right profile =
      ∑ first : SixVertexHorizontalBoundedSingleRowProfile T,
        ∑ second : SixVertexHorizontalBoundedSingleRowProfile T,
          if sixVertexHorizontalAddSingleRowProfiles first second = profile then
            sixVertexHorizontalSingleRowProfileSectorSum T left first *
              sixVertexHorizontalSingleRowProfileSectorSum T right second
          else 0 := by
  classical
  unfold sixVertexHorizontalFineRowProfileSectorPairSum
    sixVertexHorizontalSingleRowProfileSectorSum
  simp_rw [sixVertexHorizontalPairBoundedFineRowProfile_eq_add]
  exact finite_pair_fiber_factorization
    sixVertexHorizontalBoundedSingleRowProfile
    sixVertexHorizontalBoundedSingleRowProfile
    sixVertexHorizontalAddSingleRowProfiles profile
    (sixVertexHorizontalSectorCompletionChooseCount T left)
    (sixVertexHorizontalSectorCompletionChooseCount T right)


end
end StatMech.FrontierD
