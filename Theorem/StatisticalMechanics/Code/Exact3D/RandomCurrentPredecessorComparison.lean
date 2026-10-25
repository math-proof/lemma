/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

theorem finset_singleton_symmDiff_singleton_eq_pair
    {α : Type*} [DecidableEq α] {u v : α} (huv : u ≠ v) :
    ({u} : Finset α) ∆ {v} = {u, v} := by
  ext x
  simp only [Finset.mem_symmDiff, Finset.mem_singleton,
    Finset.mem_insert]
  constructor
  · intro h
    rcases h with ⟨hxu, _⟩ | ⟨hxv, _⟩
    · exact Or.inl hxu
    · exact Or.inr hxv
  · intro h
    rcases h with hxu | hxv
    · left
      exact ⟨hxu, by simpa [hxu] using huv⟩
    · right
      exact ⟨hxv, by simpa [hxv] using huv.symm⟩


theorem finsetSubtype_internal_injective_route_surjective
    {α : Type*} {Ω : Finset α}
    {route : {x : α // x ∈ Ω} → α}
    (hinj : Function.Injective route)
    (hinternal : ∀ x : {x : α // x ∈ Ω}, route x ∈ Ω)
    (y : α) (hy : y ∈ Ω) :
    ∃ x : {x : α // x ∈ Ω}, route x = y := by
  classical
  haveI : Fintype {x : α // x ∈ Ω} := Finset.Subtype.fintype Ω
  haveI : Finite {x : α // x ∈ Ω} :=
    Fintype.finite (Finset.Subtype.fintype Ω)
  let routeSubtype : {x : α // x ∈ Ω} → {x : α // x ∈ Ω} :=
    fun x => ⟨route x, hinternal x⟩
  have hinjSubtype : Function.Injective routeSubtype := by
    intro x y hxy
    apply hinj
    exact congrArg Subtype.val hxy
  have hsurjSubtype : Function.Surjective routeSubtype :=
    Finite.surjective_of_injective hinjSubtype
  rcases hsurjSubtype ⟨y, hy⟩ with ⟨x, hx⟩
  exact ⟨x, congrArg Subtype.val hx⟩


theorem finsetSubtype_internal_injective_route_sum_eq
    {α M : Type*} [AddCommMonoid M] {Ω : Finset α}
    {route : {x : α // x ∈ Ω} → α}
    (hinj : Function.Injective route)
    (hinternal : ∀ x : {x : α // x ∈ Ω}, route x ∈ Ω)
    (W : α → M) :
    (∑ x ∈ Ω.attach, W (route x)) = ∑ y ∈ Ω, W y := by
  classical
  refine Finset.sum_bij (fun x _hx => route x) ?hmem ?hinj ?hsurj ?hfun
  · intro x _hx
    exact hinternal x
  · intro x _hx y _hy hxy
    exact hinj hxy
  · intro y hy
    rcases
        finsetSubtype_internal_injective_route_surjective
          (Ω := Ω) (route := route) hinj hinternal y hy with
      ⟨x, hx⟩
    exact ⟨x, Finset.mem_attach Ω x, hx⟩
  · intro x _hx
    rfl


theorem finsetSubtype_internal_injective_route_pointwise_mul_sum_le
    {α : Type*} {Ω : Finset α}
    {route : {x : α // x ∈ Ω} → α}
    (hinj : Function.Injective route)
    (hinternal : ∀ x : {x : α // x ∈ Ω}, route x ∈ Ω)
    (F W : α → ℝ) (c : ℝ)
    (hpoint : ∀ y : α, ∀ hy : y ∈ Ω, F y ≤ c * W (route ⟨y, hy⟩)) :
    (∑ y ∈ Ω, F y) ≤ c * ∑ y ∈ Ω, W y := by
  classical
  calc
    (∑ y ∈ Ω, F y) = ∑ x ∈ Ω.attach, F x.1 := by
      exact (Finset.sum_attach Ω F).symm
    _ ≤ ∑ x ∈ Ω.attach, c * W (route x) := by
      refine Finset.sum_le_sum ?_
      intro x _hx
      exact hpoint x.1 x.2
    _ = c * ∑ y ∈ Ω, W y := by
      rw [← Finset.mul_sum]
      exact congrArg (fun z => c * z)
        (finsetSubtype_internal_injective_route_sum_eq
          (Ω := Ω) (route := route) hinj hinternal W)


theorem finsetSubtype_externalRouteImage_not_mem
    {α : Type*} [DecidableEq α] {Ω : Finset α}
    {route : {x : α // x ∈ Ω} → α}
    {y : α}
    (hy : y ∈ (Ω.attach.filter (fun x => route x ∉ Ω)).image route) :
    y ∉ Ω := by
  classical
  rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
  exact (Finset.mem_filter.mp hx).2


theorem finsetSubtype_external_route_pointwise_mul_sum_le_image_sum
    {α : Type*} [DecidableEq α] {Ω : Finset α}
    {route : {x : α // x ∈ Ω} → α}
    (hinj : Function.Injective route)
    (F W : α → ℝ) (c : ℝ)
    (hpoint :
      ∀ x : {x : α // x ∈ Ω}, route x ∉ Ω → F x.1 ≤ c * W (route x)) :
    (∑ x ∈ Ω.attach.filter (fun x => route x ∉ Ω), F x.1) ≤
      c * ∑ y ∈ (Ω.attach.filter (fun x => route x ∉ Ω)).image route,
        W y := by
  classical
  let externalRows : Finset {x : α // x ∈ Ω} :=
    Ω.attach.filter (fun x => route x ∉ Ω)
  calc
    (∑ x ∈ Ω.attach.filter (fun x => route x ∉ Ω), F x.1) ≤
        ∑ x ∈ externalRows, c * W (route x) := by
      dsimp [externalRows]
      refine Finset.sum_le_sum ?_
      intro x hx
      exact hpoint x (Finset.mem_filter.mp hx).2
    _ = c * ∑ y ∈ externalRows.image route, W y := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_image]
      intro x _hx y _hy hxy
      exact hinj hxy


theorem finsetSubtype_internal_injective_fixedPointFree_route_distinct_predecessor
    {α : Type*} {Ω : Finset α}
    {route : {x : α // x ∈ Ω} → α}
    (hinj : Function.Injective route)
    (hinternal : ∀ x : {x : α // x ∈ Ω}, route x ∈ Ω)
    (hnofixed : ∀ y : α, ∀ hy : y ∈ Ω, route ⟨y, hy⟩ ≠ y)
    (y : α) (hy : y ∈ Ω) :
    ∃ x : {x : α // x ∈ Ω}, x.1 ≠ y ∧ route x = y := by
  rcases
      finsetSubtype_internal_injective_route_surjective
        (Ω := Ω) (route := route) hinj hinternal y hy with
    ⟨x, hx⟩
  have hx_ne : x.1 ≠ y := by
    intro hxy
    have hfixed : route x = x.1 := by
      simpa [hxy] using hx
    exact (hnofixed x.1 x.2) hfixed
  exact ⟨x, hx_ne, hx⟩


end Exact3D
end StatMech
