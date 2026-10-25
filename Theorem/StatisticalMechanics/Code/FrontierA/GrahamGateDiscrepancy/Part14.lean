/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Max
import Def.StatisticalMechanics.Code.FrontierA.GrahamGateDiscrepancy.Part12


namespace StatMech.FrontierA

@[simp] theorem mem_finiteCommonClosureStep
    {A : Type*} [Fintype A] (P Q : A -> Prop) (R : A -> A -> Prop)
    (S : Finset A) (x : A) :
    x ∈ finiteCommonClosureStep P Q R S ↔
      x ∈ S ∨
        (x ∈ finiteRelationNeighborhood R S ∧ P x ∧ Q x) := by
  classical
  simp [finiteCommonClosureStep]

theorem subset_finiteCommonClosureStep
    {A : Type*} [Fintype A] (P Q : A -> Prop) (R : A -> A -> Prop)
    (S : Finset A) :
    S ⊆ finiteCommonClosureStep P Q R S := by
  classical
  exact Finset.subset_union_left

theorem finiteRelationNeighborhood_mono
    {A : Type*} [Fintype A] (R : A -> A -> Prop)
    {S T : Finset A} (hST : S ⊆ T) :
    finiteRelationNeighborhood R S ⊆ finiteRelationNeighborhood R T := by
  classical
  intro y hy
  obtain ⟨x, hx, hxy⟩ := Finset.mem_filter.mp hy |>.2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, x, hST hx, hxy⟩

theorem finiteCommonClosureStep_mono
    {A : Type*} [Fintype A] (P Q : A -> Prop) (R : A -> A -> Prop)
    {S T : Finset A} (hST : S ⊆ T) :
    finiteCommonClosureStep P Q R S ⊆
      finiteCommonClosureStep P Q R T := by
  classical
  intro x hx
  rcases Finset.mem_union.mp hx with hxS | hxCommon
  · exact Finset.mem_union_left _ (hST hxS)
  · apply Finset.mem_union_right
    have hx' := Finset.mem_filter.mp hxCommon
    exact Finset.mem_filter.mpr ⟨
      finiteRelationNeighborhood_mono R hST hx'.1, hx'.2⟩


end StatMech.FrontierA
