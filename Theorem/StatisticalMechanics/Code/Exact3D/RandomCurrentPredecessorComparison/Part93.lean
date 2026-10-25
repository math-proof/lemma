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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part85
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem finiteSupportExplicitCaseBudgetTotal_eq_zero_of_eq_empty
    {α κ : Type*} {Ω : Finset α} (caseOf : α → κ)
    (caseSet : Finset κ) (caseBudget : κ → ℝ) (hΩ : Ω = ∅) :
    finiteSupportExplicitCaseBudgetTotal Ω caseOf caseSet caseBudget = 0 := by
  classical
  subst Ω
  unfold finiteSupportExplicitCaseBudgetTotal
  simp [FinsetFiberIndex.fiber]

set_option linter.style.longLine false in


theorem finiteSupportExplicitCaseBudgetTotal_selectedEdgeCopiesSingletonCutoff_updateSelectedEdgeMultiplicity_eq_zero_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hew : ew ∈ doubledBoxOriginIncidentEdges n)
    (k : ℕ)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    {κ : Type*}
    (caseOf : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → κ)
    (caseSet : Finset κ) (caseBudget : κ → ℝ) :
    finiteSupportExplicitCaseBudgetTotal
        ((doubledBoxSelectedEdgeCopiesSingletonCutoff n e0 k).filter
          (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0))
        caseOf caseSet caseBudget =
      0 := by
  exact
    finiteSupportExplicitCaseBudgetTotal_eq_zero_of_eq_empty caseOf caseSet
      caseBudget
      (doubledBoxSelectedEdgeCopiesSingletonCutoff_filter_updateSelectedEdgeMultiplicity_eq_empty_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        hew k hedge)

set_option linter.style.longLine false in

theorem finiteSupportExplicitCaseBudgetTotal_mono {α κ : Type*}
    (Ω : Finset α) (caseOf : α → κ) (caseSet : Finset κ)
    {caseBudget relaxedBudget : κ → ℝ}
    (hrelax : ∀ c ∈ caseSet, caseBudget c ≤ relaxedBudget c) :
    finiteSupportExplicitCaseBudgetTotal Ω caseOf caseSet caseBudget ≤
      finiteSupportExplicitCaseBudgetTotal Ω caseOf caseSet relaxedBudget := by
  classical
  let I : FinsetFiberIndex κ := { α := α, domain := Ω, map := caseOf }
  unfold finiteSupportExplicitCaseBudgetTotal
  simp only
  refine Finset.sum_le_sum ?_
  intro c hc
  exact mul_le_mul_of_nonneg_left (hrelax c hc) (by positivity)

set_option linter.style.longLine false in


theorem finiteSupportExplicitCaseBudgetTotal_le_of_relaxed
    {α κ : Type*} (Ω : Finset α) (caseOf : α → κ)
    (caseSet : Finset κ) {caseBudget relaxedBudget : κ → ℝ}
    {target : ℝ}
    (hrelax : ∀ c ∈ caseSet, caseBudget c ≤ relaxedBudget c)
    (htotal :
      finiteSupportExplicitCaseBudgetTotal Ω caseOf caseSet relaxedBudget ≤
        target) :
    finiteSupportExplicitCaseBudgetTotal Ω caseOf caseSet caseBudget ≤
      target :=
  (finiteSupportExplicitCaseBudgetTotal_mono Ω caseOf caseSet hrelax).trans
    htotal

set_option linter.style.longLine false in


theorem finiteSupportCaseBudgetTotal_eq_finiteSupportExplicitCaseBudgetTotal
    {α κ : Type*} (Ω : Finset α) (caseOf : α → κ)
    (caseSet : Finset κ) (caseBudget : κ → ℝ)
    (hcover : ∀ a ∈ Ω, caseOf a ∈ caseSet) :
    finiteSupportCaseBudgetTotal Ω caseOf caseBudget =
      finiteSupportExplicitCaseBudgetTotal Ω caseOf caseSet caseBudget := by
  classical
  let I : FinsetFiberIndex κ := { α := α, domain := Ω, map := caseOf }
  let f : κ → ℝ := fun c => ((I.fiber c).card : ℝ) * caseBudget c
  have hsubset : I.image ⊆ caseSet := by
    intro c hc
    rcases (FinsetFiberIndex.mem_image I c).mp hc with
      ⟨a, ha, hmap⟩
    have haΩ : a ∈ Ω := by
      simpa [I] using ha
    have hcase : caseOf a = c := by
      simpa [I] using hmap
    simpa [hcase] using hcover a haΩ
  have hzero : ∀ c ∈ caseSet, c ∉ I.image → f c = 0 := by
    intro c _hc hnot
    have hcard : (I.fiber c).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro a ha
      rcases (FinsetFiberIndex.mem_fiber I c a).mp ha with
        ⟨hadom, hmap⟩
      exact hnot <| (FinsetFiberIndex.mem_image I c).mpr
        ⟨a, hadom, hmap⟩
    simp [f, hcard]
  change Finset.sum I.image f = Finset.sum caseSet f
  exact Finset.sum_subset hsubset hzero

set_option linter.style.longLine false in


theorem finiteSupportExplicitCaseBudgetTotal_self_eq_finset_sum
    {α : Type*} (Ω : Finset α) (caseBudget : α → ℝ) :
    finiteSupportExplicitCaseBudgetTotal Ω (fun a => a) Ω caseBudget =
      ∑ a ∈ Ω, caseBudget a := by
  classical
  rw [
    ← finiteSupportCaseBudgetTotal_eq_finiteSupportExplicitCaseBudgetTotal
      Ω (fun a => a) Ω caseBudget (by intro a ha; simpa using ha),
    ← finset_sum_caseBudget_eq_finiteSupportCaseBudgetTotal
      Ω (fun a => a) caseBudget]

set_option linter.style.longLine false in


theorem finiteSupportExplicitCaseBudgetTotal_add
    {α κ : Type*} (Ω : Finset α) (caseOf : α → κ)
    (caseSet : Finset κ) (caseBudget₁ caseBudget₂ : κ → ℝ) :
    finiteSupportExplicitCaseBudgetTotal Ω caseOf caseSet
        (fun c => caseBudget₁ c + caseBudget₂ c) =
      finiteSupportExplicitCaseBudgetTotal Ω caseOf caseSet caseBudget₁ +
        finiteSupportExplicitCaseBudgetTotal Ω caseOf caseSet caseBudget₂ := by
  classical
  unfold finiteSupportExplicitCaseBudgetTotal
  simp [mul_add, Finset.sum_add_distrib]

set_option linter.style.longLine false in


theorem finiteSupportExplicitCaseBudgetTotal_const_mul
    {α κ : Type*} (r : ℝ) (Ω : Finset α) (caseOf : α → κ)
    (caseSet : Finset κ) (caseBudget : κ → ℝ) :
    finiteSupportExplicitCaseBudgetTotal Ω caseOf caseSet
        (fun c => r * caseBudget c) =
      r * finiteSupportExplicitCaseBudgetTotal Ω caseOf caseSet
        caseBudget := by
  classical
  unfold finiteSupportExplicitCaseBudgetTotal
  simp only
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro c _hc
  ring

set_option linter.style.longLine false in


theorem finiteSupportExplicitCaseBudgetTotal_product_fst_eq
    {α κ₁ κ₂ : Type*} (Ω : Finset α)
    (caseOf₁ : α → κ₁) (caseOf₂ : α → κ₂)
    (caseSet₁ : Finset κ₁) (caseSet₂ : Finset κ₂)
    (caseBudget₁ : κ₁ → ℝ)
    (hcover₁ : ∀ a ∈ Ω, caseOf₁ a ∈ caseSet₁)
    (hcover₂ : ∀ a ∈ Ω, caseOf₂ a ∈ caseSet₂) :
    finiteSupportExplicitCaseBudgetTotal Ω
        (fun a => (caseOf₁ a, caseOf₂ a))
        (caseSet₁.product caseSet₂)
        (fun c : κ₁ × κ₂ => caseBudget₁ c.1) =
      finiteSupportExplicitCaseBudgetTotal Ω caseOf₁ caseSet₁
        caseBudget₁ := by
  classical
  have hcoverProd :
      ∀ a ∈ Ω, (caseOf₁ a, caseOf₂ a) ∈
        caseSet₁.product caseSet₂ := by
    intro a ha
    exact Finset.mem_product.mpr ⟨hcover₁ a ha, hcover₂ a ha⟩
  rw [← finiteSupportCaseBudgetTotal_eq_finiteSupportExplicitCaseBudgetTotal
      Ω (fun a => (caseOf₁ a, caseOf₂ a)) (caseSet₁.product caseSet₂)
      (fun c : κ₁ × κ₂ => caseBudget₁ c.1) hcoverProd,
    ← finiteSupportCaseBudgetTotal_eq_finiteSupportExplicitCaseBudgetTotal
      Ω caseOf₁ caseSet₁ caseBudget₁ hcover₁,
    ← finset_sum_caseBudget_eq_finiteSupportCaseBudgetTotal
      Ω (fun a => (caseOf₁ a, caseOf₂ a))
      (fun c : κ₁ × κ₂ => caseBudget₁ c.1),
    ← finset_sum_caseBudget_eq_finiteSupportCaseBudgetTotal
      Ω caseOf₁ caseBudget₁]

set_option linter.style.longLine false in

theorem finiteSupportExplicitCaseBudgetTotal_product_snd_eq
    {α κ₁ κ₂ : Type*} (Ω : Finset α)
    (caseOf₁ : α → κ₁) (caseOf₂ : α → κ₂)
    (caseSet₁ : Finset κ₁) (caseSet₂ : Finset κ₂)
    (caseBudget₂ : κ₂ → ℝ)
    (hcover₁ : ∀ a ∈ Ω, caseOf₁ a ∈ caseSet₁)
    (hcover₂ : ∀ a ∈ Ω, caseOf₂ a ∈ caseSet₂) :
    finiteSupportExplicitCaseBudgetTotal Ω
        (fun a => (caseOf₁ a, caseOf₂ a))
        (caseSet₁.product caseSet₂)
        (fun c : κ₁ × κ₂ => caseBudget₂ c.2) =
      finiteSupportExplicitCaseBudgetTotal Ω caseOf₂ caseSet₂
        caseBudget₂ := by
  classical
  have hcoverProd :
      ∀ a ∈ Ω, (caseOf₁ a, caseOf₂ a) ∈
        caseSet₁.product caseSet₂ := by
    intro a ha
    exact Finset.mem_product.mpr ⟨hcover₁ a ha, hcover₂ a ha⟩
  rw [← finiteSupportCaseBudgetTotal_eq_finiteSupportExplicitCaseBudgetTotal
      Ω (fun a => (caseOf₁ a, caseOf₂ a)) (caseSet₁.product caseSet₂)
      (fun c : κ₁ × κ₂ => caseBudget₂ c.2) hcoverProd,
    ← finiteSupportCaseBudgetTotal_eq_finiteSupportExplicitCaseBudgetTotal
      Ω caseOf₂ caseSet₂ caseBudget₂ hcover₂,
    ← finset_sum_caseBudget_eq_finiteSupportCaseBudgetTotal
      Ω (fun a => (caseOf₁ a, caseOf₂ a))
      (fun c : κ₁ × κ₂ => caseBudget₂ c.2),
    ← finset_sum_caseBudget_eq_finiteSupportCaseBudgetTotal
      Ω caseOf₂ caseBudget₂]

set_option linter.style.longLine false in


theorem finiteSupportExplicitCaseBudgetTotal_product_add_eq
    {α κ₁ κ₂ : Type*} (Ω : Finset α)
    (caseOf₁ : α → κ₁) (caseOf₂ : α → κ₂)
    (caseSet₁ : Finset κ₁) (caseSet₂ : Finset κ₂)
    (caseBudget₁ : κ₁ → ℝ) (caseBudget₂ : κ₂ → ℝ)
    (hcover₁ : ∀ a ∈ Ω, caseOf₁ a ∈ caseSet₁)
    (hcover₂ : ∀ a ∈ Ω, caseOf₂ a ∈ caseSet₂) :
    finiteSupportExplicitCaseBudgetTotal Ω
        (fun a => (caseOf₁ a, caseOf₂ a))
        (caseSet₁.product caseSet₂)
        (fun c : κ₁ × κ₂ => caseBudget₁ c.1 + caseBudget₂ c.2) =
      finiteSupportExplicitCaseBudgetTotal Ω caseOf₁ caseSet₁
          caseBudget₁ +
        finiteSupportExplicitCaseBudgetTotal Ω caseOf₂ caseSet₂
          caseBudget₂ := by
  rw [finiteSupportExplicitCaseBudgetTotal_add,
    finiteSupportExplicitCaseBudgetTotal_product_fst_eq
      Ω caseOf₁ caseOf₂ caseSet₁ caseSet₂ caseBudget₁ hcover₁ hcover₂,
    finiteSupportExplicitCaseBudgetTotal_product_snd_eq
      Ω caseOf₁ caseOf₂ caseSet₁ caseSet₂ caseBudget₂ hcover₁ hcover₂]

set_option linter.style.longLine false in


theorem finiteSupportExplicitCaseBudgetTotal_product_add_le
    {α κ₁ κ₂ : Type*} (Ω : Finset α)
    (caseOf₁ : α → κ₁) (caseOf₂ : α → κ₂)
    (caseSet₁ : Finset κ₁) (caseSet₂ : Finset κ₂)
    (caseBudget₁ : κ₁ → ℝ) (caseBudget₂ : κ₂ → ℝ)
    {target : ℝ}
    (hcover₁ : ∀ a ∈ Ω, caseOf₁ a ∈ caseSet₁)
    (hcover₂ : ∀ a ∈ Ω, caseOf₂ a ∈ caseSet₂)
    (htotal :
      finiteSupportExplicitCaseBudgetTotal Ω caseOf₁ caseSet₁
          caseBudget₁ +
        finiteSupportExplicitCaseBudgetTotal Ω caseOf₂ caseSet₂
          caseBudget₂ ≤ target) :
    finiteSupportExplicitCaseBudgetTotal Ω
        (fun a => (caseOf₁ a, caseOf₂ a))
        (caseSet₁.product caseSet₂)
        (fun c : κ₁ × κ₂ => caseBudget₁ c.1 + caseBudget₂ c.2) ≤
      target := by
  rw [finiteSupportExplicitCaseBudgetTotal_product_add_eq
    Ω caseOf₁ caseOf₂ caseSet₁ caseSet₂ caseBudget₁ caseBudget₂
    hcover₁ hcover₂]
  exact htotal

set_option linter.style.longLine false in


theorem sum_finiteSupportExplicitCaseBudgetTotal_product_fst_eq
    {α ι κ₁ κ₂ : Type*} (S : Finset ι) (Ω : ι → Finset α)
    (caseOf₁ : ι → α → κ₁) (caseOf₂ : ι → α → κ₂)
    (caseSet₁ : ι → Finset κ₁) (caseSet₂ : ι → Finset κ₂)
    (caseBudget₁ : ι → κ₁ → ℝ)
    (hcover₁ : ∀ i ∈ S, ∀ a ∈ Ω i, caseOf₁ i a ∈ caseSet₁ i)
    (hcover₂ : ∀ i ∈ S, ∀ a ∈ Ω i, caseOf₂ i a ∈ caseSet₂ i) :
    (∑ i ∈ S,
      finiteSupportExplicitCaseBudgetTotal
        (Ω i) (fun a => (caseOf₁ i a, caseOf₂ i a))
        ((caseSet₁ i).product (caseSet₂ i))
        (fun c : κ₁ × κ₂ => caseBudget₁ i c.1)) =
      ∑ i ∈ S,
        finiteSupportExplicitCaseBudgetTotal
          (Ω i) (caseOf₁ i) (caseSet₁ i) (caseBudget₁ i) := by
  refine Finset.sum_congr rfl ?_
  intro i hi
  exact
    finiteSupportExplicitCaseBudgetTotal_product_fst_eq
      (Ω i) (caseOf₁ i) (caseOf₂ i) (caseSet₁ i) (caseSet₂ i)
      (caseBudget₁ i) (hcover₁ i hi) (hcover₂ i hi)

set_option linter.style.longLine false in


theorem sum_finiteSupportExplicitCaseBudgetTotal_product_snd_eq
    {α ι κ₁ κ₂ : Type*} (S : Finset ι) (Ω : ι → Finset α)
    (caseOf₁ : ι → α → κ₁) (caseOf₂ : ι → α → κ₂)
    (caseSet₁ : ι → Finset κ₁) (caseSet₂ : ι → Finset κ₂)
    (caseBudget₂ : ι → κ₂ → ℝ)
    (hcover₁ : ∀ i ∈ S, ∀ a ∈ Ω i, caseOf₁ i a ∈ caseSet₁ i)
    (hcover₂ : ∀ i ∈ S, ∀ a ∈ Ω i, caseOf₂ i a ∈ caseSet₂ i) :
    (∑ i ∈ S,
      finiteSupportExplicitCaseBudgetTotal
        (Ω i) (fun a => (caseOf₁ i a, caseOf₂ i a))
        ((caseSet₁ i).product (caseSet₂ i))
        (fun c : κ₁ × κ₂ => caseBudget₂ i c.2)) =
      ∑ i ∈ S,
        finiteSupportExplicitCaseBudgetTotal
          (Ω i) (caseOf₂ i) (caseSet₂ i) (caseBudget₂ i) := by
  refine Finset.sum_congr rfl ?_
  intro i hi
  exact
    finiteSupportExplicitCaseBudgetTotal_product_snd_eq
      (Ω i) (caseOf₁ i) (caseOf₂ i) (caseSet₁ i) (caseSet₂ i)
      (caseBudget₂ i) (hcover₁ i hi) (hcover₂ i hi)

set_option linter.style.longLine false in


theorem sum_finiteSupportExplicitCaseBudgetTotal_product_fst_le
    {α ι κ₁ κ₂ : Type*} (S : Finset ι) (Ω : ι → Finset α)
    (caseOf₁ : ι → α → κ₁) (caseOf₂ : ι → α → κ₂)
    (caseSet₁ : ι → Finset κ₁) (caseSet₂ : ι → Finset κ₂)
    (caseBudget₁ : ι → κ₁ → ℝ) {target : ℝ}
    (hcover₁ : ∀ i ∈ S, ∀ a ∈ Ω i, caseOf₁ i a ∈ caseSet₁ i)
    (hcover₂ : ∀ i ∈ S, ∀ a ∈ Ω i, caseOf₂ i a ∈ caseSet₂ i)
    (htotal :
      (∑ i ∈ S,
        finiteSupportExplicitCaseBudgetTotal
          (Ω i) (caseOf₁ i) (caseSet₁ i) (caseBudget₁ i)) ≤
        target) :
    (∑ i ∈ S,
      finiteSupportExplicitCaseBudgetTotal
        (Ω i) (fun a => (caseOf₁ i a, caseOf₂ i a))
        ((caseSet₁ i).product (caseSet₂ i))
        (fun c : κ₁ × κ₂ => caseBudget₁ i c.1)) ≤
      target := by
  rw [sum_finiteSupportExplicitCaseBudgetTotal_product_fst_eq
    S Ω caseOf₁ caseOf₂ caseSet₁ caseSet₂ caseBudget₁ hcover₁ hcover₂]
  exact htotal

set_option linter.style.longLine false in


theorem sum_finiteSupportExplicitCaseBudgetTotal_product_snd_le
    {α ι κ₁ κ₂ : Type*} (S : Finset ι) (Ω : ι → Finset α)
    (caseOf₁ : ι → α → κ₁) (caseOf₂ : ι → α → κ₂)
    (caseSet₁ : ι → Finset κ₁) (caseSet₂ : ι → Finset κ₂)
    (caseBudget₂ : ι → κ₂ → ℝ) {target : ℝ}
    (hcover₁ : ∀ i ∈ S, ∀ a ∈ Ω i, caseOf₁ i a ∈ caseSet₁ i)
    (hcover₂ : ∀ i ∈ S, ∀ a ∈ Ω i, caseOf₂ i a ∈ caseSet₂ i)
    (htotal :
      (∑ i ∈ S,
        finiteSupportExplicitCaseBudgetTotal
          (Ω i) (caseOf₂ i) (caseSet₂ i) (caseBudget₂ i)) ≤
        target) :
    (∑ i ∈ S,
      finiteSupportExplicitCaseBudgetTotal
        (Ω i) (fun a => (caseOf₁ i a, caseOf₂ i a))
        ((caseSet₁ i).product (caseSet₂ i))
        (fun c : κ₁ × κ₂ => caseBudget₂ i c.2)) ≤
      target := by
  rw [sum_finiteSupportExplicitCaseBudgetTotal_product_snd_eq
    S Ω caseOf₁ caseOf₂ caseSet₁ caseSet₂ caseBudget₂ hcover₁ hcover₂]
  exact htotal

set_option linter.style.longLine false in


theorem finiteSupportCaseBudgetTotal_le_of_finiteSupportExplicitCaseBudgetTotal_le
    {α κ : Type*} (Ω : Finset α) (caseOf : α → κ)
    (caseSet : Finset κ) (caseBudget : κ → ℝ) {target : ℝ}
    (hcover : ∀ a ∈ Ω, caseOf a ∈ caseSet)
    (htotal :
      finiteSupportExplicitCaseBudgetTotal Ω caseOf caseSet caseBudget ≤
        target) :
    finiteSupportCaseBudgetTotal Ω caseOf caseBudget ≤ target := by
  rw [
    finiteSupportCaseBudgetTotal_eq_finiteSupportExplicitCaseBudgetTotal
      Ω caseOf caseSet caseBudget hcover]
  exact htotal

set_option linter.style.longLine false in


theorem finiteSupportExplicitCaseBudgetTotal_subset_le_of_nonneg
    {α κ : Type*} {Ω₁ Ω₂ : Finset α} (caseOf : α → κ)
    (caseSet : Finset κ) (caseBudget : κ → ℝ)
    (hsubset : Ω₁ ⊆ Ω₂)
    (hcover₂ : ∀ a ∈ Ω₂, caseOf a ∈ caseSet)
    (hnonneg : ∀ c ∈ caseSet, 0 ≤ caseBudget c) :
    finiteSupportExplicitCaseBudgetTotal Ω₁ caseOf caseSet caseBudget ≤
      finiteSupportExplicitCaseBudgetTotal Ω₂ caseOf caseSet caseBudget := by
  have hcover₁ : ∀ a ∈ Ω₁, caseOf a ∈ caseSet := by
    intro a ha
    exact hcover₂ a (hsubset ha)
  rw [← finiteSupportCaseBudgetTotal_eq_finiteSupportExplicitCaseBudgetTotal
      Ω₁ caseOf caseSet caseBudget hcover₁,
    ← finiteSupportCaseBudgetTotal_eq_finiteSupportExplicitCaseBudgetTotal
      Ω₂ caseOf caseSet caseBudget hcover₂,
    ← finset_sum_caseBudget_eq_finiteSupportCaseBudgetTotal Ω₁ caseOf
      caseBudget,
    ← finset_sum_caseBudget_eq_finiteSupportCaseBudgetTotal Ω₂ caseOf
      caseBudget]
  exact
    Finset.sum_le_sum_of_subset_of_nonneg hsubset fun a ha₂ _ha_not₁ =>
      hnonneg (caseOf a) (hcover₂ a ha₂)

set_option linter.style.longLine false in


theorem finiteSupportExplicitCaseBudgetTotal_updateSelectedEdgeMultiplicityFilter_le_originTouchesEdgeSupportFilter_of_nonneg_strictSectorYPredecessor3
    {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hew : ew ∈ doubledBoxOriginIncidentEdges n)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    {κ : Type*}
    (caseOf : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → κ)
    (caseSet : Finset κ) (caseBudget : κ → ℝ)
    (hcover :
      ∀ m ∈ Ω.filter (fun m => doubledBoxOriginTouchesEdgeSupport n m),
        caseOf m ∈ caseSet)
    (hnonneg : ∀ c ∈ caseSet, 0 ≤ caseBudget c) :
    finiteSupportExplicitCaseBudgetTotal
        (Ω.filter
          (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0))
        caseOf caseSet caseBudget ≤
      finiteSupportExplicitCaseBudgetTotal
        (Ω.filter (fun m => doubledBoxOriginTouchesEdgeSupport n m))
        caseOf caseSet caseBudget := by
  exact
    finiteSupportExplicitCaseBudgetTotal_subset_le_of_nonneg caseOf caseSet
      caseBudget
      (doubledBoxUpdateSelectedEdgeMultiplicity_filter_subset_originTouchesEdgeSupport_filter_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        hew hedge Ω)
      hcover hnonneg

set_option linter.style.longLine false in


theorem sum_finiteSupportExplicitCaseBudgetTotal_updateSelectedEdgeMultiplicityFilters_le_originTouchesEdgeSupportFilters_of_nonneg_strictSectorYPredecessor3
    {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    {κ : Type*}
    (caseOf :
      ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → κ)
    (caseSet : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → Finset κ)
    (caseBudget : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → κ → ℝ)
    (hcover :
      ∀ ew ∈ doubledBoxOriginIncidentEdges n,
        ∀ m ∈ Ω.filter (fun m => doubledBoxOriginTouchesEdgeSupport n m),
          caseOf ew m ∈ caseSet ew)
    (hnonneg :
      ∀ ew ∈ doubledBoxOriginIncidentEdges n,
        ∀ c ∈ caseSet ew, 0 ≤ caseBudget ew c) :
    (∑ ew ∈ doubledBoxOriginIncidentEdges n,
      finiteSupportExplicitCaseBudgetTotal
        (Ω.filter
          (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0))
        (caseOf ew) (caseSet ew) (caseBudget ew)) ≤
      ∑ ew ∈ doubledBoxOriginIncidentEdges n,
        finiteSupportExplicitCaseBudgetTotal
          (Ω.filter (fun m => doubledBoxOriginTouchesEdgeSupport n m))
          (caseOf ew) (caseSet ew) (caseBudget ew) := by
  refine Finset.sum_le_sum ?_
  intro ew hew
  exact
    finiteSupportExplicitCaseBudgetTotal_updateSelectedEdgeMultiplicityFilter_le_originTouchesEdgeSupportFilter_of_nonneg_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      hew hedge Ω (caseOf ew) (caseSet ew) (caseBudget ew)
      (hcover ew hew) (hnonneg ew hew)

set_option linter.style.longLine false in


theorem sum_finiteSupportExplicitCaseBudgetTotal_updateSelectedEdgeMultiplicityFilters_le_of_originTouchesEdgeSupportFilters_le_of_nonneg_strictSectorYPredecessor3
    {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    {κ : Type*}
    (caseOf :
      ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → κ)
    (caseSet : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → Finset κ)
    (caseBudget : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → κ → ℝ)
    {target : ℝ}
    (hcover :
      ∀ ew ∈ doubledBoxOriginIncidentEdges n,
        ∀ m ∈ Ω.filter (fun m => doubledBoxOriginTouchesEdgeSupport n m),
          caseOf ew m ∈ caseSet ew)
    (hnonneg :
      ∀ ew ∈ doubledBoxOriginIncidentEdges n,
        ∀ c ∈ caseSet ew, 0 ≤ caseBudget ew c)
    (htotal :
      (∑ ew ∈ doubledBoxOriginIncidentEdges n,
        finiteSupportExplicitCaseBudgetTotal
          (Ω.filter (fun m => doubledBoxOriginTouchesEdgeSupport n m))
          (caseOf ew) (caseSet ew) (caseBudget ew)) ≤ target) :
    (∑ ew ∈ doubledBoxOriginIncidentEdges n,
      finiteSupportExplicitCaseBudgetTotal
        (Ω.filter
          (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0))
        (caseOf ew) (caseSet ew) (caseBudget ew)) ≤ target :=
  (sum_finiteSupportExplicitCaseBudgetTotal_updateSelectedEdgeMultiplicityFilters_le_originTouchesEdgeSupportFilters_of_nonneg_strictSectorYPredecessor3
    (n := n) (v := v) hvwedge hlt hypos (e0 := e0) hedge Ω caseOf
    caseSet caseBudget hcover hnonneg).trans htotal

set_option linter.style.longLine false in


theorem finiteSupportExplicitCaseBudgetTotal_strictSectorYActiveUpdateSelectedEdgeMultiplicityFilter_le_activeOriginTouchesEdgeSupportFilter_of_nonneg_strictSectorYPredecessor3
    {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hew : ew ∈ doubledBoxOriginIncidentEdges n)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    {κ : Type*}
    (caseOf : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → κ)
    (caseSet : Finset κ) (caseBudget : κ → ℝ)
    (hcover :
      ∀ m ∈
        (Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => doubledBoxOriginTouchesEdgeSupport n m),
        caseOf m ∈ caseSet)
    (hnonneg : ∀ c ∈ caseSet, 0 ≤ caseBudget c) :
    finiteSupportExplicitCaseBudgetTotal
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0))
        caseOf caseSet caseBudget ≤
      finiteSupportExplicitCaseBudgetTotal
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => doubledBoxOriginTouchesEdgeSupport n m))
        caseOf caseSet caseBudget := by
  exact
    finiteSupportExplicitCaseBudgetTotal_updateSelectedEdgeMultiplicityFilter_le_originTouchesEdgeSupportFilter_of_nonneg_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      hew hedge
      (Ω.filter
        (doubledBoxIncrementedFullSourceActive n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0))
      caseOf caseSet caseBudget hcover hnonneg

set_option linter.style.longLine false in


theorem sum_finiteSupportExplicitCaseBudgetTotal_strictSectorYActiveUpdateSelectedEdgeMultiplicityFilters_le_activeOriginTouchesEdgeSupportFilters_of_nonneg_strictSectorYPredecessor3
    {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    {κ : Type*}
    (caseOf :
      ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → κ)
    (caseSet : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → Finset κ)
    (caseBudget : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → κ → ℝ)
    (hcover :
      ∀ ew ∈ doubledBoxOriginIncidentEdges n,
        ∀ m ∈
          (Ω.filter
            (doubledBoxIncrementedFullSourceActive n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
            (fun m => doubledBoxOriginTouchesEdgeSupport n m),
          caseOf ew m ∈ caseSet ew)
    (hnonneg :
      ∀ ew ∈ doubledBoxOriginIncidentEdges n,
        ∀ c ∈ caseSet ew, 0 ≤ caseBudget ew c) :
    (∑ ew ∈ doubledBoxOriginIncidentEdges n,
      finiteSupportExplicitCaseBudgetTotal
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0))
        (caseOf ew) (caseSet ew) (caseBudget ew)) ≤
      ∑ ew ∈ doubledBoxOriginIncidentEdges n,
        finiteSupportExplicitCaseBudgetTotal
          ((Ω.filter
            (doubledBoxIncrementedFullSourceActive n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
            (fun m => doubledBoxOriginTouchesEdgeSupport n m))
          (caseOf ew) (caseSet ew) (caseBudget ew) := by
  exact
    sum_finiteSupportExplicitCaseBudgetTotal_updateSelectedEdgeMultiplicityFilters_le_originTouchesEdgeSupportFilters_of_nonneg_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) hedge
      (Ω.filter
        (doubledBoxIncrementedFullSourceActive n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0))
      caseOf caseSet caseBudget hcover hnonneg

set_option linter.style.longLine false in


theorem sum_finiteSupportExplicitCaseBudgetTotal_strictSectorYActiveUpdateSelectedEdgeMultiplicityFilters_le_of_activeOriginTouchesEdgeSupportFilters_le_of_nonneg_strictSectorYPredecessor3
    {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    {κ : Type*}
    (caseOf :
      ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → κ)
    (caseSet : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → Finset κ)
    (caseBudget : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → κ → ℝ)
    {target : ℝ}
    (hcover :
      ∀ ew ∈ doubledBoxOriginIncidentEdges n,
        ∀ m ∈
          (Ω.filter
            (doubledBoxIncrementedFullSourceActive n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
            (fun m => doubledBoxOriginTouchesEdgeSupport n m),
          caseOf ew m ∈ caseSet ew)
    (hnonneg :
      ∀ ew ∈ doubledBoxOriginIncidentEdges n,
        ∀ c ∈ caseSet ew, 0 ≤ caseBudget ew c)
    (htotal :
      (∑ ew ∈ doubledBoxOriginIncidentEdges n,
        finiteSupportExplicitCaseBudgetTotal
          ((Ω.filter
            (doubledBoxIncrementedFullSourceActive n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
            (fun m => doubledBoxOriginTouchesEdgeSupport n m))
          (caseOf ew) (caseSet ew) (caseBudget ew)) ≤ target) :
    (∑ ew ∈ doubledBoxOriginIncidentEdges n,
      finiteSupportExplicitCaseBudgetTotal
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0))
        (caseOf ew) (caseSet ew) (caseBudget ew)) ≤ target :=
  (sum_finiteSupportExplicitCaseBudgetTotal_strictSectorYActiveUpdateSelectedEdgeMultiplicityFilters_le_activeOriginTouchesEdgeSupportFilters_of_nonneg_strictSectorYPredecessor3
    (n := n) (v := v) hvwedge hlt hypos (e0 := e0) hedge Ω caseOf
    caseSet caseBudget hcover hnonneg).trans htotal

set_option linter.style.longLine false in


theorem sum_finiteSupportExplicitCaseBudgetTotal_subset_le_of_nonneg
    {α ι κ : Type*} (S : Finset ι)
    (Ω₁ Ω₂ : ι → Finset α)
    (caseOf : ι → α → κ) (caseSet : ι → Finset κ)
    (caseBudget : ι → κ → ℝ)
    (hsubset : ∀ i ∈ S, Ω₁ i ⊆ Ω₂ i)
    (hcover₂ : ∀ i ∈ S, ∀ a ∈ Ω₂ i, caseOf i a ∈ caseSet i)
    (hnonneg : ∀ i ∈ S, ∀ c ∈ caseSet i, 0 ≤ caseBudget i c) :
    (∑ i ∈ S,
      finiteSupportExplicitCaseBudgetTotal
        (Ω₁ i) (caseOf i) (caseSet i) (caseBudget i)) ≤
      ∑ i ∈ S,
        finiteSupportExplicitCaseBudgetTotal
          (Ω₂ i) (caseOf i) (caseSet i) (caseBudget i) := by
  refine Finset.sum_le_sum ?_
  intro i hi
  exact
    finiteSupportExplicitCaseBudgetTotal_subset_le_of_nonneg
      (caseOf i) (caseSet i) (caseBudget i) (hsubset i hi)
      (hcover₂ i hi) (hnonneg i hi)

set_option linter.style.longLine false in


theorem finset_sum_le_of_finiteSupportExplicitCaseBudgetTotal_le
    {α κ : Type*} (Ω : Finset α) (F : α → ℝ) (caseOf : α → κ)
    (caseSet : Finset κ) (caseBudget : κ → ℝ) {target : ℝ}
    (hcover : ∀ a ∈ Ω, caseOf a ∈ caseSet)
    (hpoint : ∀ a ∈ Ω, F a ≤ caseBudget (caseOf a))
    (htotal :
      finiteSupportExplicitCaseBudgetTotal Ω caseOf caseSet caseBudget ≤
        target) :
    Finset.sum Ω F ≤ target :=
  finset_sum_le_of_finiteSupportCaseBudgetTotal_le Ω F caseOf caseBudget
    hpoint
    (finiteSupportCaseBudgetTotal_le_of_finiteSupportExplicitCaseBudgetTotal_le
      Ω caseOf caseSet caseBudget hcover htotal)

set_option linter.style.longLine false in


theorem finset_sum_le_of_finiteSupportExplicitCaseBudgetTotal_le_of_relaxed
    {α κ : Type*} (Ω : Finset α) (F : α → ℝ) (caseOf : α → κ)
    (caseSet : Finset κ) (rowBound relaxedBudget : κ → ℝ) {target : ℝ}
    (hcover : ∀ a ∈ Ω, caseOf a ∈ caseSet)
    (hpoint : ∀ a ∈ Ω, F a ≤ rowBound (caseOf a))
    (hrelax : ∀ c ∈ caseSet, rowBound c ≤ relaxedBudget c)
    (htotal :
      finiteSupportExplicitCaseBudgetTotal Ω caseOf caseSet relaxedBudget ≤
        target) :
    Finset.sum Ω F ≤ target := by
  refine
    finset_sum_le_of_finiteSupportExplicitCaseBudgetTotal_le Ω F caseOf
      caseSet relaxedBudget hcover ?_ htotal
  intro a ha
  exact (hpoint a ha).trans (hrelax (caseOf a) (hcover a ha))

set_option linter.style.longLine false in


theorem finset_sum_le_sum_filter_cover_of_nonneg
    {α ι : Type*} (Ω : Finset α) (S : Finset ι)
    (R : ι → α → Prop) [∀ i, DecidablePred (R i)]
    (F : α → ℝ)
    (hzero : ∀ a ∈ Ω, (∀ i ∈ S, ¬ R i a) → F a = 0)
    (hnonneg : ∀ a ∈ Ω, 0 ≤ F a) :
    (∑ a ∈ Ω, F a) ≤
      ∑ i ∈ S, ∑ a ∈ Ω.filter (R i), F a := by
  have hpoint :
      ∀ a ∈ Ω, F a ≤ ∑ i ∈ S, if R i a then F a else 0 := by
    intro a ha
    by_cases hcovered : ∃ i ∈ S, R i a
    · rcases hcovered with ⟨i, hi, hRi⟩
      have hterm_nonneg :
          ∀ j ∈ S, 0 ≤ if R j a then F a else 0 := by
        intro j _hj
        by_cases hRj : R j a
        · simpa [hRj] using hnonneg a ha
        · simp [hRj]
      have hsingle :
          (if R i a then F a else 0) ≤
            ∑ j ∈ S, if R j a then F a else 0 :=
        Finset.single_le_sum hterm_nonneg hi
      simpa [hRi] using hsingle
    · have hnone : ∀ i ∈ S, ¬ R i a := by
        intro i hi hRi
        exact hcovered ⟨i, hi, hRi⟩
      rw [hzero a ha hnone]
      exact Finset.sum_nonneg fun i _hi => by
        by_cases hRi : R i a
        · simp [hRi]
        · simp [hRi]
  calc
    (∑ a ∈ Ω, F a) ≤
        ∑ a ∈ Ω, ∑ i ∈ S, if R i a then F a else 0 :=
      Finset.sum_le_sum hpoint
    _ = ∑ i ∈ S, ∑ a ∈ Ω, if R i a then F a else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ i ∈ S, ∑ a ∈ Ω.filter (R i), F a := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      rw [Finset.sum_filter]

set_option linter.style.longLine false in


theorem doubledBoxOriginTouchesEdgeSupport_finset_sum_le_sum_originIncidentEdgeFilters
    {n : ℕ}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (F : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ)
    (hzero :
      ∀ m ∈ Ω, ¬ doubledBoxOriginTouchesEdgeSupport n m → F m = 0)
    (hnonneg : ∀ m ∈ Ω, 0 ≤ F m) :
    (∑ m ∈ Ω, F m) ≤
      ∑ e ∈ doubledBoxOriginIncidentEdges n,
        ∑ m ∈ Ω.filter (fun m => m e ≠ 0), F m := by
  refine
    finset_sum_le_sum_filter_cover_of_nonneg Ω
      (doubledBoxOriginIncidentEdges n) (fun e m => m e ≠ 0) F ?_
      hnonneg
  intro m hm hnone
  exact hzero m hm <| by
    rw [doubledBoxOriginTouchesEdgeSupport_iff_exists_originIncidentEdge]
    rintro ⟨e, he, hme⟩
    exact hnone e he hme

set_option linter.style.longLine false in


theorem finset_sum_le_of_doubledBoxOriginIncidentEdgeWitnessFilters_finiteSupportExplicitCaseBudgetTotal_le_of_relaxed
    {n : ℕ} {κ : Type*}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (F : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ)
    (caseOf :
      ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → κ)
    (caseSet : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → Finset κ)
    (rowBound relaxedBudget :
      ↥(FK.boxGraph 3 (2 * n)).edgeFinset → κ → ℝ)
    {target : ℝ}
    (hzero :
      ∀ m ∈ Ω, ¬ doubledBoxOriginTouchesEdgeSupport n m → F m = 0)
    (hnonneg : ∀ m ∈ Ω, 0 ≤ F m)
    (hcover :
      ∀ e ∈ doubledBoxOriginIncidentEdges n,
        ∀ m ∈ Ω.filter (fun m => m e ≠ 0),
          caseOf e m ∈ caseSet e)
    (hpoint :
      ∀ e ∈ doubledBoxOriginIncidentEdges n,
        ∀ m ∈ Ω.filter (fun m => m e ≠ 0),
          F m ≤ rowBound e (caseOf e m))
    (hrelax :
      ∀ e ∈ doubledBoxOriginIncidentEdges n,
        ∀ c ∈ caseSet e, rowBound e c ≤ relaxedBudget e c)
    (htotal :
      (∑ e ∈ doubledBoxOriginIncidentEdges n,
        finiteSupportExplicitCaseBudgetTotal
          (Ω.filter (fun m => m e ≠ 0))
          (caseOf e) (caseSet e) (relaxedBudget e)) ≤ target) :
    (∑ m ∈ Ω, F m) ≤ target := by
  calc
    (∑ m ∈ Ω, F m) ≤
        ∑ e ∈ doubledBoxOriginIncidentEdges n,
          ∑ m ∈ Ω.filter (fun m => m e ≠ 0), F m :=
      doubledBoxOriginTouchesEdgeSupport_finset_sum_le_sum_originIncidentEdgeFilters
        Ω F hzero hnonneg
    _ ≤
        ∑ e ∈ doubledBoxOriginIncidentEdges n,
          finiteSupportExplicitCaseBudgetTotal
            (Ω.filter (fun m => m e ≠ 0))
            (caseOf e) (caseSet e) (relaxedBudget e) := by
      refine Finset.sum_le_sum ?_
      intro e he
      exact
        finset_sum_le_of_finiteSupportExplicitCaseBudgetTotal_le_of_relaxed
          (Ω.filter (fun m => m e ≠ 0)) F (caseOf e) (caseSet e)
            (rowBound e) (relaxedBudget e) (hcover e he) (hpoint e he)
          (hrelax e he) le_rfl
    _ ≤ target := htotal

set_option linter.style.longLine false in


theorem finset_sum_le_of_doubledBoxOriginIncidentSupportPatternFilters_finiteSupportExplicitCaseBudgetTotal_le_of_relaxed
    {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    {κ : Type*}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (F : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ)
    (caseOf :
      Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → κ)
    (caseSet : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset → Finset κ)
    (rowBound relaxedBudget :
      Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset → κ → ℝ)
    {target : ℝ}
    (hcover :
      ∀ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
          (fun S => S.Nonempty),
        ∀ m ∈ Ω.filter
          (fun m => doubledBoxOriginIncidentSupport n m = S),
          caseOf S m ∈ caseSet S)
    (hpoint :
      ∀ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
          (fun S => S.Nonempty),
        ∀ m ∈ Ω.filter
          (fun m => doubledBoxOriginIncidentSupport n m = S),
          F m ≤ rowBound S (caseOf S m))
    (hrelax :
      ∀ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
          (fun S => S.Nonempty),
        ∀ c ∈ caseSet S, rowBound S c ≤ relaxedBudget S c)
    (htotal :
      (∑ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
          (fun S => S.Nonempty),
        finiteSupportExplicitCaseBudgetTotal
          (Ω.filter (fun m => doubledBoxOriginIncidentSupport n m = S))
          (caseOf S) (caseSet S) (relaxedBudget S)) ≤ target) :
    (∑ m ∈ Ω.filter (fun m => doubledBoxOriginTouchesEdgeSupport n m), F m) ≤
      target := by
  calc
    (∑ m ∈ Ω.filter (fun m => doubledBoxOriginTouchesEdgeSupport n m), F m) =
        ∑ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
            (fun S => S.Nonempty),
          ∑ m ∈ Ω.filter
            (fun m => doubledBoxOriginIncidentSupport n m = S),
            F m :=
      doubledBoxOriginTouchesEdgeSupport_filter_sum_eq_sum_nonempty_originIncidentSupportPatternFilters
        Ω F
    _ ≤
        ∑ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
            (fun S => S.Nonempty),
          finiteSupportExplicitCaseBudgetTotal
            (Ω.filter (fun m => doubledBoxOriginIncidentSupport n m = S))
            (caseOf S) (caseSet S) (relaxedBudget S) := by
      refine Finset.sum_le_sum ?_
      intro S hS
      exact
        finset_sum_le_of_finiteSupportExplicitCaseBudgetTotal_le_of_relaxed
          (Ω.filter (fun m => doubledBoxOriginIncidentSupport n m = S))
          F (caseOf S) (caseSet S) (rowBound S) (relaxedBudget S)
          (hcover S hS) (hpoint S hS) (hrelax S hS) le_rfl
    _ ≤ target := htotal

set_option linter.style.longLine false in


theorem finset_sum_eq_sum_owner_filter_of_zero_none
    {α ι : Type*} [DecidableEq ι] (Ω : Finset α) (S : Finset ι)
    (owner : α → Option ι) (F : α → ℝ)
    (hzero : ∀ a ∈ Ω, owner a = none → F a = 0)
    (howner_mem : ∀ a ∈ Ω, ∀ i, owner a = some i → i ∈ S) :
    (∑ a ∈ Ω, F a) =
      ∑ i ∈ S, ∑ a ∈ Ω.filter (fun a => owner a = some i), F a := by
  have hpoint :
      ∀ a ∈ Ω, F a =
        ∑ i ∈ S, if owner a = some i then F a else 0 := by
    intro a ha
    cases hown : owner a with
    | none =>
        rw [hzero a ha hown]
        simp
    | some i =>
        have hiS : i ∈ S := howner_mem a ha i hown
        have hsum :
            (∑ j ∈ S, if (some i : Option ι) = some j then F a else 0) =
              F a := by
          refine
            (Finset.sum_eq_single_of_mem
              (s := S)
              (f := fun j =>
                if (some i : Option ι) = some j then F a else 0)
              i hiS ?_).trans ?_
          · intro j _hj hji
            have hnot : ¬ (some i : Option ι) = some j := by
              intro hj
              exact hji (Option.some.inj hj.symm)
            simp [hnot]
          · simp
        exact hsum.symm
  calc
    (∑ a ∈ Ω, F a) =
        ∑ a ∈ Ω, ∑ i ∈ S, if owner a = some i then F a else 0 := by
      exact Finset.sum_congr rfl hpoint
    _ = ∑ i ∈ S, ∑ a ∈ Ω, if owner a = some i then F a else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ i ∈ S, ∑ a ∈ Ω.filter (fun a => owner a = some i), F a := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      rw [Finset.sum_filter]

set_option linter.style.longLine false in


theorem doubledBoxIncrementedFullSourceActive_finset_sum_eq_sum_originIncidentOwnerFilters_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (F : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ) :
    (∑ m ∈
      Ω.filter
        (doubledBoxIncrementedFullSourceActive n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0),
      F m) =
      ∑ ew ∈ doubledBoxOriginIncidentEdges n,
        ∑ m ∈
          (Ω.filter
            (doubledBoxIncrementedFullSourceActive n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
            (fun m => doubledBoxOriginIncidentOwner n m = some ew),
          F m := by
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  exact
    finset_sum_eq_sum_owner_filter_of_zero_none
      (Ω.filter (doubledBoxIncrementedFullSourceActive n w e0))
      (doubledBoxOriginIncidentEdges n)
      (doubledBoxOriginIncidentOwner n) F
      (by
        intro m hm hnone
        have hactive :
            doubledBoxIncrementedFullSourceActive n w e0 m :=
          (Finset.mem_filter.mp hm).2
        have htouch : doubledBoxOriginTouchesEdgeSupport n m :=
          doubledBoxIncrementedFullSourceActive_originTouchesEdgeSupport_of_strictSectorYPredecessor3
            (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (m := m)
            (by simpa [w] using hedge) (by simpa [w] using hactive)
        have hnot :
            ¬ doubledBoxOriginTouchesEdgeSupport n m :=
          (doubledBoxOriginIncidentOwner_eq_none_iff_not_originTouchesEdgeSupport
            (n := n) (m := m)).1 hnone
        exact False.elim (hnot htouch))
      (by
        intro m _hm ew howner
        exact
          (doubledBoxOriginIncidentOwner_spec_of_eq_some
            (n := n) (m := m) (e := ew) howner).1)

set_option linter.style.longLine false in


theorem beta_mul_edgeCopySourcePairEmptySummand_finset_sum_le_switchedSourceSectorResidualMomentEmptyBranchSummand_sum_of_strictSectorYActive
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    β *
        (∑ m ∈
          Ω.filter
            (doubledBoxIncrementedFullSourceActive n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0),
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) m) ≤
      ∑ m ∈
        Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0),
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m := by
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let F : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ := fun m =>
    edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
      (doubledBoxOriginToInnerEndpointSource n v)
      (∅ : Finset (FK.boxVerts 3 (2 * n))) m
  let R : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ := fun m =>
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w e0 m
  have hF :=
    doubledBoxIncrementedFullSourceActive_finset_sum_eq_sum_originIncidentOwnerFilters_of_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) hedge Ω F
  have hR :=
    doubledBoxIncrementedFullSourceActive_finset_sum_eq_sum_originIncidentOwnerFilters_of_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) hedge Ω R
  calc
    β * (∑ m ∈ Ω.filter (doubledBoxIncrementedFullSourceActive n w e0),
        F m) =
        β *
          (∑ ew ∈ doubledBoxOriginIncidentEdges n,
            ∑ m ∈
              (Ω.filter
                (doubledBoxIncrementedFullSourceActive n w e0)).filter
                (fun m => doubledBoxOriginIncidentOwner n m = some ew),
              F m) := by
          rw [hF]
    _ =
        ∑ ew ∈ doubledBoxOriginIncidentEdges n,
          β *
            (∑ m ∈
              (Ω.filter
                (doubledBoxIncrementedFullSourceActive n w e0)).filter
                (fun m => doubledBoxOriginIncidentOwner n m = some ew),
              F m) := by
          rw [Finset.mul_sum]
    _ ≤
        ∑ ew ∈ doubledBoxOriginIncidentEdges n,
          ∑ m ∈
            (Ω.filter
              (doubledBoxIncrementedFullSourceActive n w e0)).filter
              (fun m => doubledBoxOriginIncidentOwner n m = some ew),
            R m := by
          refine Finset.sum_le_sum ?_
          intro ew _hew
          exact
            beta_mul_edgeCopySourcePairEmptySummand_finset_sum_le_switchedSourceSectorResidualMomentEmptyBranchSummand_sum_of_strictSectorYActiveOwnerFilter
              (β := β) hβ (n := n) (v := v) hvwedge hlt hypos
              (e0 := e0) (ew := ew) hedge Ω
    _ =
        ∑ m ∈ Ω.filter (doubledBoxIncrementedFullSourceActive n w e0),
          R m := by
          rw [hR]

set_option linter.style.longLine false in


theorem beta_mul_edgeCopySourcePairInnerPairSummand_finset_sum_le_switchedSourceSectorResidualMomentInnerPairBranchSummand_sum_of_strictSectorYActive
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    β *
        (∑ m ∈
          Ω.filter
            (doubledBoxIncrementedFullSourceActive n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0),
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
            (doubledBoxInnerPairSource n v
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) m) ≤
      ∑ m ∈
        Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0),
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m := by
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let F : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ := fun m =>
    edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
      (doubledBoxOriginToInnerEndpointSource n w)
      (doubledBoxInnerPairSource n v w) m
  let R : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ := fun m =>
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v w
      e0 m
  have hF :=
    doubledBoxIncrementedFullSourceActive_finset_sum_eq_sum_originIncidentOwnerFilters_of_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) hedge Ω F
  have hR :=
    doubledBoxIncrementedFullSourceActive_finset_sum_eq_sum_originIncidentOwnerFilters_of_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) hedge Ω R
  calc
    β * (∑ m ∈ Ω.filter (doubledBoxIncrementedFullSourceActive n w e0),
        F m) =
        β *
          (∑ ew ∈ doubledBoxOriginIncidentEdges n,
            ∑ m ∈
              (Ω.filter
                (doubledBoxIncrementedFullSourceActive n w e0)).filter
                (fun m => doubledBoxOriginIncidentOwner n m = some ew),
              F m) := by
          rw [hF]
    _ =
        ∑ ew ∈ doubledBoxOriginIncidentEdges n,
          β *
            (∑ m ∈
              (Ω.filter
                (doubledBoxIncrementedFullSourceActive n w e0)).filter
                (fun m => doubledBoxOriginIncidentOwner n m = some ew),
              F m) := by
          rw [Finset.mul_sum]
    _ ≤
        ∑ ew ∈ doubledBoxOriginIncidentEdges n,
          ∑ m ∈
            (Ω.filter
              (doubledBoxIncrementedFullSourceActive n w e0)).filter
              (fun m => doubledBoxOriginIncidentOwner n m = some ew),
            R m := by
          refine Finset.sum_le_sum ?_
          intro ew _hew
          exact
            beta_mul_edgeCopySourcePairInnerPairSummand_finset_sum_le_switchedSourceSectorResidualMomentInnerPairBranchSummand_sum_of_strictSectorYActiveOwnerFilter
              (β := β) hβ (n := n) (v := v) hvwedge hlt hypos
              (e0 := e0) (ew := ew) hedge Ω
    _ =
        ∑ m ∈ Ω.filter (doubledBoxIncrementedFullSourceActive n w e0),
          R m := by
          rw [hR]

set_option linter.style.longLine false in


theorem doubledBoxStrictSectorYActive_exists_ownerContainingCardResidualPayments_finset_sum_le
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    let G := FK.boxGraph 3 (2 * n)
    let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
    let A := doubledBoxOriginToInnerEndpointSource n v
    let Ωactive :=
      Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
    let Ωowner := fun ew : ↥G.edgeFinset =>
      Ωactive.filter (fun m => doubledBoxOriginIncidentOwner n m = some ew)
    ∃ selected owner :
      ∀ ew : ↥G.edgeFinset,
        ∀ m : ↥G.edgeFinset → ℕ,
          Sharpness.FluxEdgeCopy.Copy G (Function.update m e0 (m e0 + 1)),
      (∀ ew ∈ doubledBoxOriginIncidentEdges n, ∀ m ∈ Ωowner ew,
        (selected ew m).1 = e0 ∧
          (owner ew m).1 = ew ∧
          (edgeCopySourceSectorContainingBothCopies G A
                (Function.update m e0 (m e0 + 1)) (owner ew m)
                (selected ew m)).card +
              (edgeCopySourceSectorContainingAndExcludingCopy G A
                (Function.update m e0 (m e0 + 1)) (owner ew m)
                (selected ew m)).card =
            (edgeCopySourceSectorContainingCopy G A
              (Function.update m e0 (m e0 + 1)) (owner ew m)).card ∧
          0 <
            (edgeCopySourceSectorContainingCopy G A
              (Function.update m e0 (m e0 + 1)) (owner ew m)).card) ∧
        (∑ ew ∈ doubledBoxOriginIncidentEdges n,
          β *
            (∑ m ∈ Ωowner ew,
              (((edgeCopySourceSectorContainingCopy G A
                  (Function.update m e0 (m e0 + 1))
                  (owner ew m)).card : ℝ) *
                edgeCopySourcePairSummand G β (fun _ => 1)
                  (doubledBoxOriginToInnerEndpointSource n v)
                  (∅ : Finset (FK.boxVerts 3 (2 * n))) m))) ≤
          ∑ m ∈ Ωactive,
            doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n
              v w e0 m ∧
        (∑ ew ∈ doubledBoxOriginIncidentEdges n,
          β *
            (∑ m ∈ Ωowner ew,
              (((edgeCopySourceSectorContainingCopy G A
                  (Function.update m e0 (m e0 + 1))
                  (owner ew m)).card : ℝ) *
                edgeCopySourcePairSummand G β (fun _ => 1)
                  (doubledBoxOriginToInnerEndpointSource n w)
                  (doubledBoxInnerPairSource n v w) m))) ≤
          ∑ m ∈ Ωactive,
            doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
              β n v w e0 m := by
  classical
  let G := FK.boxGraph 3 (2 * n)
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let A := doubledBoxOriginToInnerEndpointSource n v
  let Ωactive : Finset (↥G.edgeFinset → ℕ) :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let Ωowner : ↥G.edgeFinset → Finset (↥G.edgeFinset → ℕ) :=
    fun ew =>
      Ωactive.filter (fun m => doubledBoxOriginIncidentOwner n m = some ew)
  let hpack := fun ew =>
    doubledBoxStrictSectorYActiveOwnerFilter_exists_commonSelectedOwnerContainingCardResidualPayments_finset_sum
      (β := β) hβ (n := n) (v := v) hvwedge hlt hypos
      (e0 := e0) (ew := ew) hedge Ω
  let selected :
      ∀ ew : ↥G.edgeFinset,
        ∀ m : ↥G.edgeFinset → ℕ,
          Sharpness.FluxEdgeCopy.Copy G
            (Function.update m e0 (m e0 + 1)) :=
    fun ew => Classical.choose (hpack ew)
  let owner :
      ∀ ew : ↥G.edgeFinset,
        ∀ m : ↥G.edgeFinset → ℕ,
          Sharpness.FluxEdgeCopy.Copy G
            (Function.update m e0 (m e0 + 1)) :=
    fun ew => Classical.choose (Classical.choose_spec (hpack ew))
  have hrow :
      ∀ ew ∈ doubledBoxOriginIncidentEdges n, ∀ m ∈ Ωowner ew,
        (selected ew m).1 = e0 ∧
          (owner ew m).1 = ew ∧
          (edgeCopySourceSectorContainingBothCopies G A
                (Function.update m e0 (m e0 + 1)) (owner ew m)
                (selected ew m)).card +
              (edgeCopySourceSectorContainingAndExcludingCopy G A
                (Function.update m e0 (m e0 + 1)) (owner ew m)
                (selected ew m)).card =
            (edgeCopySourceSectorContainingCopy G A
              (Function.update m e0 (m e0 + 1)) (owner ew m)).card ∧
          0 <
            (edgeCopySourceSectorContainingCopy G A
              (Function.update m e0 (m e0 + 1)) (owner ew m)).card := by
    intro ew _hew m hm
    exact (Classical.choose_spec
      (Classical.choose_spec (hpack ew))).1 m hm
  have hemptyOwnerSum :
      (∑ ew ∈ doubledBoxOriginIncidentEdges n,
        β *
          (∑ m ∈ Ωowner ew,
            (((edgeCopySourceSectorContainingCopy G A
                (Function.update m e0 (m e0 + 1))
                (owner ew m)).card : ℝ) *
              edgeCopySourcePairSummand G β (fun _ => 1)
                (doubledBoxOriginToInnerEndpointSource n v)
                (∅ : Finset (FK.boxVerts 3 (2 * n))) m))) ≤
        ∑ ew ∈ doubledBoxOriginIncidentEdges n,
          ∑ m ∈ Ωowner ew,
            doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n
              v w e0 m := by
    refine Finset.sum_le_sum ?_
    intro ew _hew
    exact (Classical.choose_spec
      (Classical.choose_spec (hpack ew))).2.1
  have hinnerOwnerSum :
      (∑ ew ∈ doubledBoxOriginIncidentEdges n,
        β *
          (∑ m ∈ Ωowner ew,
            (((edgeCopySourceSectorContainingCopy G A
                (Function.update m e0 (m e0 + 1))
                (owner ew m)).card : ℝ) *
              edgeCopySourcePairSummand G β (fun _ => 1)
                (doubledBoxOriginToInnerEndpointSource n w)
                (doubledBoxInnerPairSource n v w) m))) ≤
        ∑ ew ∈ doubledBoxOriginIncidentEdges n,
          ∑ m ∈ Ωowner ew,
            doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
              β n v w e0 m := by
    refine Finset.sum_le_sum ?_
    intro ew _hew
    exact (Classical.choose_spec
      (Classical.choose_spec (hpack ew))).2.2
  let Rempty : (↥G.edgeFinset → ℕ) → ℝ := fun m =>
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w e0
      m
  let Rinner : (↥G.edgeFinset → ℕ) → ℝ := fun m =>
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v w
      e0 m
  have hRempty :=
    doubledBoxIncrementedFullSourceActive_finset_sum_eq_sum_originIncidentOwnerFilters_of_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) hedge Ω Rempty
  have hRinner :=
    doubledBoxIncrementedFullSourceActive_finset_sum_eq_sum_originIncidentOwnerFilters_of_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) hedge Ω Rinner
  refine ⟨selected, owner, hrow, ?_, ?_⟩
  · calc
      (∑ ew ∈ doubledBoxOriginIncidentEdges n,
        β *
          (∑ m ∈ Ωowner ew,
            (((edgeCopySourceSectorContainingCopy G A
                (Function.update m e0 (m e0 + 1))
                (owner ew m)).card : ℝ) *
              edgeCopySourcePairSummand G β (fun _ => 1)
                (doubledBoxOriginToInnerEndpointSource n v)
                (∅ : Finset (FK.boxVerts 3 (2 * n))) m))) ≤
          ∑ ew ∈ doubledBoxOriginIncidentEdges n,
            ∑ m ∈ Ωowner ew,
              doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                β n v w e0 m :=
        hemptyOwnerSum
      _ =
          ∑ m ∈ Ωactive,
            doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n
              v w e0 m := by
        simpa [G, w, Ωactive, Ωowner, Rempty] using hRempty.symm
  · calc
      (∑ ew ∈ doubledBoxOriginIncidentEdges n,
        β *
          (∑ m ∈ Ωowner ew,
            (((edgeCopySourceSectorContainingCopy G A
                (Function.update m e0 (m e0 + 1))
                (owner ew m)).card : ℝ) *
              edgeCopySourcePairSummand G β (fun _ => 1)
                (doubledBoxOriginToInnerEndpointSource n w)
                (doubledBoxInnerPairSource n v w) m))) ≤
          ∑ ew ∈ doubledBoxOriginIncidentEdges n,
            ∑ m ∈ Ωowner ew,
              doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                β n v w e0 m :=
        hinnerOwnerSum
      _ =
          ∑ m ∈ Ωactive,
            doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
              β n v w e0 m := by
        simpa [G, w, Ωactive, Ωowner, Rinner] using hRinner.symm

set_option linter.style.longLine false in


theorem finset_sum_le_of_ownerFilters_finiteSupportExplicitCaseBudgetTotal_le_of_relaxed
    {α ι κ : Type*} [DecidableEq ι] (Ω : Finset α) (S : Finset ι)
    (owner : α → Option ι) (F : α → ℝ)
    (caseOf : ι → α → κ) (caseSet : ι → Finset κ)
    (rowBound relaxedBudget : ι → κ → ℝ) {target : ℝ}
    (hzero : ∀ a ∈ Ω, owner a = none → F a = 0)
    (howner_mem : ∀ a ∈ Ω, ∀ i, owner a = some i → i ∈ S)
    (hcover :
      ∀ i ∈ S, ∀ a ∈ Ω.filter (fun a => owner a = some i),
        caseOf i a ∈ caseSet i)
    (hpoint :
      ∀ i ∈ S, ∀ a ∈ Ω.filter (fun a => owner a = some i),
        F a ≤ rowBound i (caseOf i a))
    (hrelax :
      ∀ i ∈ S, ∀ c ∈ caseSet i, rowBound i c ≤ relaxedBudget i c)
    (htotal :
      (∑ i ∈ S,
        finiteSupportExplicitCaseBudgetTotal
          (Ω.filter (fun a => owner a = some i))
          (caseOf i) (caseSet i) (relaxedBudget i)) ≤ target) :
    (∑ a ∈ Ω, F a) ≤ target := by
  calc
    (∑ a ∈ Ω, F a) =
        ∑ i ∈ S, ∑ a ∈ Ω.filter (fun a => owner a = some i), F a :=
      finset_sum_eq_sum_owner_filter_of_zero_none Ω S owner F hzero
        howner_mem
    _ ≤
        ∑ i ∈ S,
          finiteSupportExplicitCaseBudgetTotal
            (Ω.filter (fun a => owner a = some i))
            (caseOf i) (caseSet i) (relaxedBudget i) := by
      refine Finset.sum_le_sum ?_
      intro i hi
      exact
        finset_sum_le_of_finiteSupportExplicitCaseBudgetTotal_le_of_relaxed
          (Ω.filter (fun a => owner a = some i)) F (caseOf i)
          (caseSet i) (rowBound i) (relaxedBudget i) (hcover i hi)
          (hpoint i hi) (hrelax i hi) le_rfl
    _ ≤ target := htotal

set_option linter.style.longLine false in


theorem finset_sum_le_of_ownerFilters_witnessFilters_finiteSupportExplicitCaseBudgetTotal_le_of_relaxed_of_nonneg
    {α ι κ : Type*} [DecidableEq ι] (Ω : Finset α) (S : Finset ι)
    (owner : α → Option ι)
    (R : ι → α → Prop) [∀ i, DecidablePred (R i)]
    (F : α → ℝ)
    (caseOf : ι → α → κ) (caseSet : ι → Finset κ)
    (rowBound relaxedBudget : ι → κ → ℝ) {target : ℝ}
    (hzero : ∀ a ∈ Ω, owner a = none → F a = 0)
    (howner_mem : ∀ a ∈ Ω, ∀ i, owner a = some i → i ∈ S)
    (howner_subset :
      ∀ i ∈ S,
        Ω.filter (fun a => owner a = some i) ⊆ Ω.filter (R i))
    (hcover :
      ∀ i ∈ S, ∀ a ∈ Ω.filter (R i), caseOf i a ∈ caseSet i)
    (hpoint :
      ∀ i ∈ S, ∀ a ∈ Ω.filter (R i),
        F a ≤ rowBound i (caseOf i a))
    (hrelax :
      ∀ i ∈ S, ∀ c ∈ caseSet i, rowBound i c ≤ relaxedBudget i c)
    (hnonneg :
      ∀ i ∈ S, ∀ c ∈ caseSet i, 0 ≤ relaxedBudget i c)
    (htotal :
      (∑ i ∈ S,
        finiteSupportExplicitCaseBudgetTotal
          (Ω.filter (R i)) (caseOf i) (caseSet i)
          (relaxedBudget i)) ≤ target) :
    (∑ a ∈ Ω, F a) ≤ target := by
  refine
    finset_sum_le_of_ownerFilters_finiteSupportExplicitCaseBudgetTotal_le_of_relaxed
      Ω S owner F caseOf caseSet rowBound relaxedBudget hzero howner_mem
      ?_ ?_ hrelax ?_
  · intro i hi a ha
    exact hcover i hi a (howner_subset i hi ha)
  · intro i hi a ha
    exact hpoint i hi a (howner_subset i hi ha)
  · exact
      (sum_finiteSupportExplicitCaseBudgetTotal_subset_le_of_nonneg S
        (fun i => Ω.filter (fun a => owner a = some i))
        (fun i => Ω.filter (R i)) caseOf caseSet relaxedBudget
        howner_subset hcover hnonneg).trans htotal

set_option linter.style.longLine false in


theorem finset_sum_le_of_doubledBoxOriginIncidentEdgeOwnerFilters_finiteSupportExplicitCaseBudgetTotal_le_of_relaxed
    {n : ℕ} {κ : Type*}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (F : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ)
    (caseOf :
      ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → κ)
    (caseSet : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → Finset κ)
    (rowBound relaxedBudget :
      ↥(FK.boxGraph 3 (2 * n)).edgeFinset → κ → ℝ)
    {target : ℝ}
    (hzero :
      ∀ m ∈ Ω, ¬ doubledBoxOriginTouchesEdgeSupport n m → F m = 0)
    (hcover :
      ∀ e ∈ doubledBoxOriginIncidentEdges n,
        ∀ m ∈ Ω.filter
            (fun m => doubledBoxOriginIncidentOwner n m = some e),
          caseOf e m ∈ caseSet e)
    (hpoint :
      ∀ e ∈ doubledBoxOriginIncidentEdges n,
        ∀ m ∈ Ω.filter
            (fun m => doubledBoxOriginIncidentOwner n m = some e),
          F m ≤ rowBound e (caseOf e m))
    (hrelax :
      ∀ e ∈ doubledBoxOriginIncidentEdges n,
        ∀ c ∈ caseSet e, rowBound e c ≤ relaxedBudget e c)
    (htotal :
      (∑ e ∈ doubledBoxOriginIncidentEdges n,
        finiteSupportExplicitCaseBudgetTotal
          (Ω.filter
            (fun m => doubledBoxOriginIncidentOwner n m = some e))
          (caseOf e) (caseSet e) (relaxedBudget e)) ≤ target) :
    (∑ m ∈ Ω, F m) ≤ target := by
  refine
    finset_sum_le_of_ownerFilters_finiteSupportExplicitCaseBudgetTotal_le_of_relaxed
      Ω (doubledBoxOriginIncidentEdges n) (doubledBoxOriginIncidentOwner n)
      F caseOf caseSet rowBound relaxedBudget ?_ ?_ hcover hpoint hrelax
      htotal
  · intro m hm howner_none
    exact hzero m hm <|
      (doubledBoxOriginIncidentOwner_eq_none_iff_not_originTouchesEdgeSupport
        (n := n) (m := m)).1 howner_none
  · intro m _hm e howner
    exact (doubledBoxOriginIncidentOwner_spec_of_eq_some
      (n := n) (m := m) (e := e) howner).1

set_option linter.style.longLine false in


theorem finset_sum_le_of_doubledBoxOriginIncidentEdgeOwnerFilters_multiplicityFilters_finiteSupportExplicitCaseBudgetTotal_le_of_relaxed_of_nonneg
    {n : ℕ} {κ : Type*}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (F : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ)
    (caseOf :
      ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → κ)
    (caseSet : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → Finset κ)
    (rowBound relaxedBudget :
      ↥(FK.boxGraph 3 (2 * n)).edgeFinset → κ → ℝ)
    {target : ℝ}
    (hzero :
      ∀ m ∈ Ω, ¬ doubledBoxOriginTouchesEdgeSupport n m → F m = 0)
    (hcover :
      ∀ e ∈ doubledBoxOriginIncidentEdges n,
        ∀ m ∈ Ω.filter (fun m => m e ≠ 0),
          caseOf e m ∈ caseSet e)
    (hpoint :
      ∀ e ∈ doubledBoxOriginIncidentEdges n,
        ∀ m ∈ Ω.filter (fun m => m e ≠ 0),
          F m ≤ rowBound e (caseOf e m))
    (hrelax :
      ∀ e ∈ doubledBoxOriginIncidentEdges n,
        ∀ c ∈ caseSet e, rowBound e c ≤ relaxedBudget e c)
    (hnonneg :
      ∀ e ∈ doubledBoxOriginIncidentEdges n,
        ∀ c ∈ caseSet e, 0 ≤ relaxedBudget e c)
    (htotal :
      (∑ e ∈ doubledBoxOriginIncidentEdges n,
        finiteSupportExplicitCaseBudgetTotal
          (Ω.filter (fun m => m e ≠ 0))
          (caseOf e) (caseSet e) (relaxedBudget e)) ≤ target) :
    (∑ m ∈ Ω, F m) ≤ target := by
  refine
    finset_sum_le_of_ownerFilters_witnessFilters_finiteSupportExplicitCaseBudgetTotal_le_of_relaxed_of_nonneg
      Ω (doubledBoxOriginIncidentEdges n) (doubledBoxOriginIncidentOwner n)
      (fun e m => m e ≠ 0) F caseOf caseSet rowBound relaxedBudget ?_ ?_
      ?_ hcover hpoint hrelax hnonneg htotal
  · intro m hm howner_none
    exact hzero m hm <|
      (doubledBoxOriginIncidentOwner_eq_none_iff_not_originTouchesEdgeSupport
        (n := n) (m := m)).1 howner_none
  · intro m _hm e howner
    exact (doubledBoxOriginIncidentOwner_spec_of_eq_some
      (n := n) (m := m) (e := e) howner).1
  · intro e _he
    exact doubledBoxOriginIncidentOwner_filter_subset_multiplicity_filter
      (n := n) Ω e

set_option linter.style.longLine false in


theorem finiteSupportExplicitCaseBudgetTotal_doubledBoxOriginIncidentOwnerFilter_le_multiplicityFilter_of_nonneg
    {n : ℕ} {κ : Type*}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (e : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (caseOf : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → κ)
    (caseSet : Finset κ) (caseBudget : κ → ℝ)
    (hcover :
      ∀ m ∈ Ω.filter (fun m => m e ≠ 0), caseOf m ∈ caseSet)
    (hnonneg : ∀ c ∈ caseSet, 0 ≤ caseBudget c) :
    finiteSupportExplicitCaseBudgetTotal
        (Ω.filter (fun m => doubledBoxOriginIncidentOwner n m = some e))
        caseOf caseSet caseBudget ≤
      finiteSupportExplicitCaseBudgetTotal
        (Ω.filter (fun m => m e ≠ 0))
        caseOf caseSet caseBudget := by
  exact
    finiteSupportExplicitCaseBudgetTotal_subset_le_of_nonneg caseOf caseSet
      caseBudget
      (doubledBoxOriginIncidentOwner_filter_subset_multiplicity_filter
        (n := n) Ω e)
      hcover hnonneg

set_option linter.style.longLine false in


theorem sum_finiteSupportExplicitCaseBudgetTotal_doubledBoxOriginIncidentOwnerFilters_le_multiplicityFilters_of_nonneg
    {n : ℕ} {κ : Type*}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (caseOf :
      ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → κ)
    (caseSet : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → Finset κ)
    (caseBudget :
      ↥(FK.boxGraph 3 (2 * n)).edgeFinset → κ → ℝ)
    (hcover :
      ∀ e ∈ doubledBoxOriginIncidentEdges n,
        ∀ m ∈ Ω.filter (fun m => m e ≠ 0),
          caseOf e m ∈ caseSet e)
    (hnonneg :
      ∀ e ∈ doubledBoxOriginIncidentEdges n,
        ∀ c ∈ caseSet e, 0 ≤ caseBudget e c) :
    (∑ e ∈ doubledBoxOriginIncidentEdges n,
      finiteSupportExplicitCaseBudgetTotal
        (Ω.filter
          (fun m => doubledBoxOriginIncidentOwner n m = some e))
        (caseOf e) (caseSet e) (caseBudget e)) ≤
      ∑ e ∈ doubledBoxOriginIncidentEdges n,
        finiteSupportExplicitCaseBudgetTotal
          (Ω.filter (fun m => m e ≠ 0))
          (caseOf e) (caseSet e) (caseBudget e) := by
  refine Finset.sum_le_sum ?_
  intro e he
  exact
    finiteSupportExplicitCaseBudgetTotal_doubledBoxOriginIncidentOwnerFilter_le_multiplicityFilter_of_nonneg
      (n := n) Ω e (caseOf e) (caseSet e) (caseBudget e)
      (hcover e he) (hnonneg e he)

set_option linter.style.longLine false in


theorem sum_finiteSupportExplicitCaseBudgetTotal_doubledBoxOriginIncidentOwnerFilters_le_of_multiplicityFilters_le_of_nonneg
    {n : ℕ} {κ : Type*}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (caseOf :
      ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → κ)
    (caseSet : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → Finset κ)
    (caseBudget :
      ↥(FK.boxGraph 3 (2 * n)).edgeFinset → κ → ℝ)
    {target : ℝ}
    (hcover :
      ∀ e ∈ doubledBoxOriginIncidentEdges n,
        ∀ m ∈ Ω.filter (fun m => m e ≠ 0),
          caseOf e m ∈ caseSet e)
    (hnonneg :
      ∀ e ∈ doubledBoxOriginIncidentEdges n,
        ∀ c ∈ caseSet e, 0 ≤ caseBudget e c)
    (htotal :
      (∑ e ∈ doubledBoxOriginIncidentEdges n,
        finiteSupportExplicitCaseBudgetTotal
          (Ω.filter (fun m => m e ≠ 0))
          (caseOf e) (caseSet e) (caseBudget e)) ≤ target) :
    (∑ e ∈ doubledBoxOriginIncidentEdges n,
      finiteSupportExplicitCaseBudgetTotal
        (Ω.filter
          (fun m => doubledBoxOriginIncidentOwner n m = some e))
        (caseOf e) (caseSet e) (caseBudget e)) ≤ target :=
  (sum_finiteSupportExplicitCaseBudgetTotal_doubledBoxOriginIncidentOwnerFilters_le_multiplicityFilters_of_nonneg
    (n := n) Ω caseOf caseSet caseBudget hcover hnonneg).trans htotal

set_option linter.style.longLine false in


theorem finiteSupportExplicitCaseBudgetTotal_strictSectorYActiveOriginIncidentOwnerFilter_le_updateSelectedEdgeMultiplicityFilter_of_nonneg
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    {κ : Type*}
    (caseOf : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → κ)
    (caseSet : Finset κ) (caseBudget : κ → ℝ)
    (hcover :
      ∀ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
        caseOf m ∈ caseSet)
    (hnonneg : ∀ c ∈ caseSet, 0 ≤ caseBudget c) :
    finiteSupportExplicitCaseBudgetTotal
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => doubledBoxOriginIncidentOwner n m = some ew))
        caseOf caseSet caseBudget ≤
      finiteSupportExplicitCaseBudgetTotal
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0))
        caseOf caseSet caseBudget := by
  exact
    finiteSupportExplicitCaseBudgetTotal_subset_le_of_nonneg caseOf caseSet
      caseBudget
      (doubledBoxIncrementedFullSourceActive_originIncidentOwner_filter_subset_updateSelectedEdge_multiplicity_filter_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        hedge Ω)
      hcover hnonneg

set_option linter.style.longLine false in


theorem finiteSupportExplicitCaseBudgetTotal_strictSectorYActiveOriginIncidentSupportPatternOwnerFilter_le_updateSelectedEdgeMultiplicityFilter_of_nonneg
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    {κ : Type*}
    (caseOf : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → κ)
    (caseSet : Finset κ) (caseBudget : κ → ℝ)
    (hcover :
      ∀ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
        caseOf m ∈ caseSet)
    (hnonneg : ∀ c ∈ caseSet, 0 ≤ caseBudget c) :
    finiteSupportExplicitCaseBudgetTotal
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m =>
            doubledBoxOriginIncidentSupport n m = S ∧
              doubledBoxOriginIncidentOwner n m = some ew))
        caseOf caseSet caseBudget ≤
      finiteSupportExplicitCaseBudgetTotal
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0))
        caseOf caseSet caseBudget := by
  exact
    finiteSupportExplicitCaseBudgetTotal_subset_le_of_nonneg caseOf caseSet
      caseBudget
      (doubledBoxIncrementedFullSourceActive_originIncidentSupportPatternOwner_filter_subset_updateSelectedEdge_multiplicity_filter_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        (S := S) hedge Ω)
      hcover hnonneg

set_option linter.style.longLine false in


theorem sum_finiteSupportExplicitCaseBudgetTotal_strictSectorYActiveOriginIncidentSupportPatternOwnerFilters_le_updateSelectedEdgeMultiplicityFilters_of_nonneg
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    {κ : Type*}
    (caseOf :
      ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → κ)
    (caseSet : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → Finset κ)
    (caseBudget : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → κ → ℝ)
    (hcover :
      ∀ ew ∈ S,
        ∀ m ∈
          ((Ω.filter
            (doubledBoxIncrementedFullSourceActive n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
            (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
          caseOf ew m ∈ caseSet ew)
    (hnonneg :
      ∀ ew ∈ S, ∀ c ∈ caseSet ew, 0 ≤ caseBudget ew c) :
    (∑ ew ∈ S,
      finiteSupportExplicitCaseBudgetTotal
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m =>
            doubledBoxOriginIncidentSupport n m = S ∧
              doubledBoxOriginIncidentOwner n m = some ew))
        (caseOf ew) (caseSet ew) (caseBudget ew)) ≤
      ∑ ew ∈ S,
        finiteSupportExplicitCaseBudgetTotal
          ((Ω.filter
            (doubledBoxIncrementedFullSourceActive n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
            (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0))
          (caseOf ew) (caseSet ew) (caseBudget ew) := by
  refine Finset.sum_le_sum ?_
  intro ew hew
  exact
    finiteSupportExplicitCaseBudgetTotal_strictSectorYActiveOriginIncidentSupportPatternOwnerFilter_le_updateSelectedEdgeMultiplicityFilter_of_nonneg
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      (S := S) hedge Ω (caseOf ew) (caseSet ew) (caseBudget ew)
      (hcover ew hew) (hnonneg ew hew)

set_option linter.style.longLine false in


theorem sum_finiteSupportExplicitCaseBudgetTotal_strictSectorYActiveOriginIncidentSupportPatternOwnerFilters_le_of_updateSelectedEdgeMultiplicityFilters_le_of_nonneg
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    {κ : Type*}
    (caseOf :
      ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → κ)
    (caseSet : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → Finset κ)
    (caseBudget : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → κ → ℝ)
    {target : ℝ}
    (hcover :
      ∀ ew ∈ S,
        ∀ m ∈
          ((Ω.filter
            (doubledBoxIncrementedFullSourceActive n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
            (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
          caseOf ew m ∈ caseSet ew)
    (hnonneg :
      ∀ ew ∈ S, ∀ c ∈ caseSet ew, 0 ≤ caseBudget ew c)
    (htotal :
      (∑ ew ∈ S,
        finiteSupportExplicitCaseBudgetTotal
          ((Ω.filter
            (doubledBoxIncrementedFullSourceActive n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
            (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0))
          (caseOf ew) (caseSet ew) (caseBudget ew)) ≤ target) :
    (∑ ew ∈ S,
      finiteSupportExplicitCaseBudgetTotal
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m =>
            doubledBoxOriginIncidentSupport n m = S ∧
              doubledBoxOriginIncidentOwner n m = some ew))
        (caseOf ew) (caseSet ew) (caseBudget ew)) ≤ target :=
  (sum_finiteSupportExplicitCaseBudgetTotal_strictSectorYActiveOriginIncidentSupportPatternOwnerFilters_le_updateSelectedEdgeMultiplicityFilters_of_nonneg
    (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (S := S)
    hedge Ω caseOf caseSet caseBudget hcover hnonneg).trans htotal

set_option linter.style.longLine false in


theorem sum_finiteSupportExplicitCaseBudgetTotal_strictSectorYActiveOriginIncidentSupportPatternOwnerFilters_allPatterns_le_updateSelectedEdgeMultiplicityFilters_of_nonneg
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    {κ : Type*}
    (caseOf :
      Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
          (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → κ)
    (caseSet :
      Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset → Finset κ)
    (caseBudget :
      Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset → κ → ℝ)
    (hcover :
      ∀ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
          (fun S => S.Nonempty),
        ∀ ew ∈ S,
          ∀ m ∈
            ((Ω.filter
              (doubledBoxIncrementedFullSourceActive n
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
                e0)).filter
              (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
            caseOf S ew m ∈ caseSet S ew)
    (hnonneg :
      ∀ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
          (fun S => S.Nonempty),
        ∀ ew ∈ S, ∀ c ∈ caseSet S ew, 0 ≤ caseBudget S ew c) :
    (∑ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
        (fun S => S.Nonempty),
      ∑ ew ∈ S,
        finiteSupportExplicitCaseBudgetTotal
          ((Ω.filter
            (doubledBoxIncrementedFullSourceActive n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
              e0)).filter
            (fun m =>
              doubledBoxOriginIncidentSupport n m = S ∧
                doubledBoxOriginIncidentOwner n m = some ew))
          (caseOf S ew) (caseSet S ew) (caseBudget S ew)) ≤
      ∑ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
          (fun S => S.Nonempty),
        ∑ ew ∈ S,
          finiteSupportExplicitCaseBudgetTotal
            ((Ω.filter
              (doubledBoxIncrementedFullSourceActive n
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
                e0)).filter
              (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0))
            (caseOf S ew) (caseSet S ew) (caseBudget S ew) := by
  refine Finset.sum_le_sum ?_
  intro S hS
  exact
    sum_finiteSupportExplicitCaseBudgetTotal_strictSectorYActiveOriginIncidentSupportPatternOwnerFilters_le_updateSelectedEdgeMultiplicityFilters_of_nonneg
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (S := S)
      hedge Ω (caseOf S) (caseSet S) (caseBudget S)
      (hcover S hS) (hnonneg S hS)

set_option linter.style.longLine false in


theorem sum_finiteSupportExplicitCaseBudgetTotal_strictSectorYActiveOriginIncidentSupportPatternOwnerFilters_allPatterns_le_of_updateSelectedEdgeMultiplicityFilters_le_of_nonneg
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    {κ : Type*}
    (caseOf :
      Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
          (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → κ)
    (caseSet :
      Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset → Finset κ)
    (caseBudget :
      Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset → κ → ℝ)
    {target : ℝ}
    (hcover :
      ∀ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
          (fun S => S.Nonempty),
        ∀ ew ∈ S,
          ∀ m ∈
            ((Ω.filter
              (doubledBoxIncrementedFullSourceActive n
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
                e0)).filter
              (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
            caseOf S ew m ∈ caseSet S ew)
    (hnonneg :
      ∀ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
          (fun S => S.Nonempty),
        ∀ ew ∈ S, ∀ c ∈ caseSet S ew, 0 ≤ caseBudget S ew c)
    (htotal :
      (∑ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
          (fun S => S.Nonempty),
        ∑ ew ∈ S,
          finiteSupportExplicitCaseBudgetTotal
            ((Ω.filter
              (doubledBoxIncrementedFullSourceActive n
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
                e0)).filter
              (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0))
            (caseOf S ew) (caseSet S ew) (caseBudget S ew)) ≤ target) :
    (∑ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
        (fun S => S.Nonempty),
      ∑ ew ∈ S,
        finiteSupportExplicitCaseBudgetTotal
          ((Ω.filter
            (doubledBoxIncrementedFullSourceActive n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
              e0)).filter
            (fun m =>
              doubledBoxOriginIncidentSupport n m = S ∧
                doubledBoxOriginIncidentOwner n m = some ew))
          (caseOf S ew) (caseSet S ew) (caseBudget S ew)) ≤ target :=
  (sum_finiteSupportExplicitCaseBudgetTotal_strictSectorYActiveOriginIncidentSupportPatternOwnerFilters_allPatterns_le_updateSelectedEdgeMultiplicityFilters_of_nonneg
    (n := n) (v := v) hvwedge hlt hypos (e0 := e0) hedge Ω caseOf
    caseSet caseBudget hcover hnonneg).trans htotal

set_option linter.style.longLine false in


theorem sum_doubledBoxIncrementedFullSourceActive_originIncidentSupportPatternOwnerBudget_le_updateSelectedEdgeMultiplicityBudget_sum_of_nonneg_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (B :
      Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
          (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ)
    (hnonneg :
      ∀ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
          (fun S => S.Nonempty),
        ∀ ew ∈ S,
          ∀ m ∈
            ((Ω.filter
              (doubledBoxIncrementedFullSourceActive n
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
                e0)).filter
              (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
            0 ≤ B S ew m) :
    (∑ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
        (fun S => S.Nonempty),
      ∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => doubledBoxOriginIncidentSupport n m = S)),
        match doubledBoxOriginIncidentOwner n m with
        | none => 0
        | some ew => B S ew m) ≤
      ∑ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
          (fun S => S.Nonempty),
        ∑ ew ∈ S,
          ∑ m ∈
            ((Ω.filter
              (doubledBoxIncrementedFullSourceActive n
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
                e0)).filter
              (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
            B S ew m := by
  classical
  let active :
      (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → Prop :=
    doubledBoxIncrementedFullSourceActive n
      (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
  let supportPatterns : Finset (Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :=
    ((doubledBoxOriginIncidentEdges n).powerset).filter
      (fun S => S.Nonempty)
  refine Finset.sum_le_sum ?_
  intro S hS
  have hSnonempty : S.Nonempty := (Finset.mem_filter.mp hS).2
  let F : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ :=
    fun m =>
      match doubledBoxOriginIncidentOwner n m with
      | none => 0
      | some ew => B S ew m
  calc
    (∑ m ∈
      ((Ω.filter active).filter
        (fun m => doubledBoxOriginIncidentSupport n m = S)),
      F m) =
        ∑ ew ∈ S,
          ∑ m ∈
            (Ω.filter active).filter
              (fun m =>
                doubledBoxOriginIncidentSupport n m = S ∧
                  doubledBoxOriginIncidentOwner n m = some ew),
            F m := by
      exact
        doubledBoxOriginIncidentSupport_filter_sum_eq_sum_supportPatternOwnerFilters
          (n := n) (Ω.filter active) hSnonempty F
    _ ≤
        ∑ ew ∈ S,
          ∑ m ∈
            (Ω.filter active).filter
              (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0),
            B S ew m := by
      refine Finset.sum_le_sum ?_
      intro ew hew
      calc
        (∑ m ∈
          (Ω.filter active).filter
            (fun m =>
              doubledBoxOriginIncidentSupport n m = S ∧
                doubledBoxOriginIncidentOwner n m = some ew),
          F m) =
            ∑ m ∈
              (Ω.filter active).filter
                (fun m =>
                  doubledBoxOriginIncidentSupport n m = S ∧
                    doubledBoxOriginIncidentOwner n m = some ew),
              B S ew m := by
          refine Finset.sum_congr rfl ?_
          intro m hm
          rw [Finset.mem_filter] at hm
          simp [F, hm.2.2]
        _ ≤
            ∑ m ∈
              (Ω.filter active).filter
                (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0),
              B S ew m :=
          doubledBoxIncrementedFullSourceActive_originIncidentSupportPatternOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_nonneg_strictSectorYPredecessor3
            (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
            (S := S) hedge Ω (B S ew)
            (by
              intro m hm
              exact hnonneg S hS ew hew m (by simpa [active] using hm))

set_option linter.style.longLine false in


theorem sum_doubledBoxIncrementedFullSourceActive_originIncidentSupportPatternOwnerBudget_le_of_updateSelectedEdgeMultiplicityBudget_sum_le_of_nonneg_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (B :
      Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
          (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ)
    {target : ℝ}
    (hnonneg :
      ∀ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
          (fun S => S.Nonempty),
        ∀ ew ∈ S,
          ∀ m ∈
            ((Ω.filter
              (doubledBoxIncrementedFullSourceActive n
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
                e0)).filter
              (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
            0 ≤ B S ew m)
    (htotal :
      (∑ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
          (fun S => S.Nonempty),
        ∑ ew ∈ S,
          ∑ m ∈
            ((Ω.filter
              (doubledBoxIncrementedFullSourceActive n
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
                e0)).filter
              (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
            B S ew m) ≤ target) :
    (∑ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
        (fun S => S.Nonempty),
      ∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => doubledBoxOriginIncidentSupport n m = S)),
        match doubledBoxOriginIncidentOwner n m with
        | none => 0
        | some ew => B S ew m) ≤ target :=
  (sum_doubledBoxIncrementedFullSourceActive_originIncidentSupportPatternOwnerBudget_le_updateSelectedEdgeMultiplicityBudget_sum_of_nonneg_strictSectorYPredecessor3
    (n := n) (v := v) hvwedge hlt hypos (e0 := e0) hedge Ω B
    hnonneg).trans htotal

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge_activeOriginIncidentSupportPatterns_sum_le_updateSelectedEdgeMultiplicityResidualBudget_sum_of_strictSectorYPredecessor3
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
        (fun S => S.Nonempty),
      ∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => doubledBoxOriginIncidentSupport n m = S)),
        match doubledBoxOriginIncidentOwner n m with
        | none => 0
        | some ew =>
            β *
              doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge
                β n v
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
                e0 ew m) ≤
      ∑ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
          (fun S => S.Nonempty),
        ∑ ew ∈ S,
          ∑ m ∈
            ((Ω.filter
              (doubledBoxIncrementedFullSourceActive n
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
                e0)).filter
              (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
            doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge
              β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
              e0 ew m := by
  classical
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let active :
      (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → Prop :=
    doubledBoxIncrementedFullSourceActive n w e0
  let patterns : Finset (Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :=
    ((doubledBoxOriginIncidentEdges n).powerset).filter
      (fun S => S.Nonempty)
  let B :
      Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
          (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ :=
    fun _S ew m =>
      β *
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge
          β n v w e0 ew m
  have htransport :
      (∑ S ∈ patterns,
        ∑ m ∈ (Ω.filter active).filter
            (fun m => doubledBoxOriginIncidentSupport n m = S),
          match doubledBoxOriginIncidentOwner n m with
          | none => 0
          | some ew => B S ew m) ≤
        ∑ S ∈ patterns,
          ∑ ew ∈ S,
            ∑ m ∈ (Ω.filter active).filter
                (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0),
              B S ew m := by
    simpa [patterns, active, w, B] using
      sum_doubledBoxIncrementedFullSourceActive_originIncidentSupportPatternOwnerBudget_le_updateSelectedEdgeMultiplicityBudget_sum_of_nonneg_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) hedge Ω B
        (by
          intro S hS ew hew m hm
          exact
            mul_nonneg hβ
              (doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge_nonneg
                hβ e0 ew m))
  have hresidual :
      (∑ S ∈ patterns,
        ∑ ew ∈ S,
          ∑ m ∈ (Ω.filter active).filter
              (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0),
            B S ew m) ≤
        ∑ S ∈ patterns,
          ∑ ew ∈ S,
            ∑ m ∈ (Ω.filter active).filter
                (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0),
              doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge
                β n v w e0 ew m := by
    refine Finset.sum_le_sum ?_
    intro S _hS
    refine Finset.sum_le_sum ?_
    intro ew _hew
    refine Finset.sum_le_sum ?_
    intro m _hm
    exact
      beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge_le_switchedSourceSectorResidualMomentAtEdge
        hβ e0 ew m
  simpa [patterns, active, w, B] using htransport.trans hresidual

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge_activeOriginIncidentSupportPatterns_sum_le_updateSelectedEdgeMultiplicityResidualBudget_sum_of_strictSectorYPredecessor3
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
        (fun S => S.Nonempty),
      ∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => doubledBoxOriginIncidentSupport n m = S)),
        match doubledBoxOriginIncidentOwner n m with
        | none => 0
        | some ew =>
            β *
              doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge
                β n v
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
                e0 ew m) ≤
      ∑ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
          (fun S => S.Nonempty),
        ∑ ew ∈ S,
          ∑ m ∈
            ((Ω.filter
              (doubledBoxIncrementedFullSourceActive n
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
                e0)).filter
              (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
            doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
              β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
              e0 ew m := by
  classical
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let active :
      (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → Prop :=
    doubledBoxIncrementedFullSourceActive n w e0
  let patterns : Finset (Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :=
    ((doubledBoxOriginIncidentEdges n).powerset).filter
      (fun S => S.Nonempty)
  let B :
      Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
          (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ :=
    fun _S ew m =>
      β *
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge
          β n v w e0 ew m
  have htransport :
      (∑ S ∈ patterns,
        ∑ m ∈ (Ω.filter active).filter
            (fun m => doubledBoxOriginIncidentSupport n m = S),
          match doubledBoxOriginIncidentOwner n m with
          | none => 0
          | some ew => B S ew m) ≤
        ∑ S ∈ patterns,
          ∑ ew ∈ S,
            ∑ m ∈ (Ω.filter active).filter
                (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0),
              B S ew m := by
    simpa [patterns, active, w, B] using
      sum_doubledBoxIncrementedFullSourceActive_originIncidentSupportPatternOwnerBudget_le_updateSelectedEdgeMultiplicityBudget_sum_of_nonneg_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) hedge Ω B
        (by
          intro S hS ew hew m hm
          exact
            mul_nonneg hβ
              (doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge_nonneg
                hβ e0 ew m))
  have hresidual :
      (∑ S ∈ patterns,
        ∑ ew ∈ S,
          ∑ m ∈ (Ω.filter active).filter
              (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0),
            B S ew m) ≤
        ∑ S ∈ patterns,
          ∑ ew ∈ S,
            ∑ m ∈ (Ω.filter active).filter
                (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0),
              doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
                β n v w e0 ew m := by
    refine Finset.sum_le_sum ?_
    intro S _hS
    refine Finset.sum_le_sum ?_
    intro ew _hew
    refine Finset.sum_le_sum ?_
    intro m _hm
    exact
      beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge_le_switchedSourceSectorResidualMomentAtEdge
        hβ e0 ew m
  simpa [patterns, active, w, B] using htransport.trans hresidual

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge_activeOriginIncidentSupportPatterns_sum_le_of_updateSelectedEdgeMultiplicity_residual_pair_sums_le_div_384_strictSectorYPredecessor3
    {β target : ℝ} (hβ : 0 ≤ β) (htarget : 0 ≤ target)
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (hpair :
      ∀ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
          (fun S => S.Nonempty),
        ∀ ew ∈ S,
          (∑ m ∈
            ((Ω.filter
              (doubledBoxIncrementedFullSourceActive n
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
                e0)).filter
              (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
            doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge
              β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
              e0 ew m) ≤ target / 384) :
    (∑ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
        (fun S => S.Nonempty),
      ∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => doubledBoxOriginIncidentSupport n m = S)),
        match doubledBoxOriginIncidentOwner n m with
        | none => 0
        | some ew =>
            β *
              doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge
                β n v
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
                e0 ew m) ≤ target := by
  classical
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let active := doubledBoxIncrementedFullSourceActive n w e0
  let patterns : Finset (Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :=
    ((doubledBoxOriginIncidentEdges n).powerset).filter
      (fun S => S.Nonempty)
  have htransport :
      (∑ S ∈ patterns,
        ∑ m ∈ (Ω.filter active).filter
            (fun m => doubledBoxOriginIncidentSupport n m = S),
          match doubledBoxOriginIncidentOwner n m with
          | none => 0
          | some ew =>
              β *
                doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge
                  β n v w e0 ew m) ≤
        ∑ S ∈ patterns,
          ∑ ew ∈ S,
            ∑ m ∈ (Ω.filter active).filter
                (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0),
              doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge
                β n v w e0 ew m := by
    simpa [patterns, active, w] using
      beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge_activeOriginIncidentSupportPatterns_sum_le_updateSelectedEdgeMultiplicityResidualBudget_sum_of_strictSectorYPredecessor3
        (β := β) hβ (n := n) (v := v) hvwedge hlt hypos
        (e0 := e0) hedge Ω
  have hpairSum :
      (∑ S ∈ patterns,
        ∑ ew ∈ S,
          ∑ m ∈ (Ω.filter active).filter
              (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0),
            doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge
              β n v w e0 ew m) ≤ target := by
    simpa [patterns, active, w] using
      doubledBoxNonemptyOriginIncidentSupportPatternOwnerPairs_sum_le_of_forall_le_div_384
        (n := n)
        (F := fun S ew =>
          ∑ m ∈ (Ω.filter active).filter
              (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0),
            doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge
              β n v w e0 ew m)
        (target := target) htarget
        (by
          intro S hS ew hew
          exact hpair S (by simpa [patterns] using hS) ew hew)
  simpa [patterns, active, w] using htransport.trans hpairSum

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge_activeOriginIncidentSupportPatterns_sum_le_of_updateSelectedEdgeMultiplicity_residual_pair_sums_le_div_384_strictSectorYPredecessor3
    {β target : ℝ} (hβ : 0 ≤ β) (htarget : 0 ≤ target)
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (hpair :
      ∀ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
          (fun S => S.Nonempty),
        ∀ ew ∈ S,
          (∑ m ∈
            ((Ω.filter
              (doubledBoxIncrementedFullSourceActive n
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
                e0)).filter
              (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
            doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
              β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
              e0 ew m) ≤ target / 384) :
    (∑ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
        (fun S => S.Nonempty),
      ∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => doubledBoxOriginIncidentSupport n m = S)),
        match doubledBoxOriginIncidentOwner n m with
        | none => 0
        | some ew =>
            β *
              doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge
                β n v
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
                e0 ew m) ≤ target := by
  classical
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let active := doubledBoxIncrementedFullSourceActive n w e0
  let patterns : Finset (Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :=
    ((doubledBoxOriginIncidentEdges n).powerset).filter
      (fun S => S.Nonempty)
  have htransport :
      (∑ S ∈ patterns,
        ∑ m ∈ (Ω.filter active).filter
            (fun m => doubledBoxOriginIncidentSupport n m = S),
          match doubledBoxOriginIncidentOwner n m with
          | none => 0
          | some ew =>
              β *
                doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge
                  β n v w e0 ew m) ≤
        ∑ S ∈ patterns,
          ∑ ew ∈ S,
            ∑ m ∈ (Ω.filter active).filter
                (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0),
              doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
                β n v w e0 ew m := by
    simpa [patterns, active, w] using
      beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge_activeOriginIncidentSupportPatterns_sum_le_updateSelectedEdgeMultiplicityResidualBudget_sum_of_strictSectorYPredecessor3
        (β := β) hβ (n := n) (v := v) hvwedge hlt hypos
        (e0 := e0) hedge Ω
  have hpairSum :
      (∑ S ∈ patterns,
        ∑ ew ∈ S,
          ∑ m ∈ (Ω.filter active).filter
              (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0),
            doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
              β n v w e0 ew m) ≤ target := by
    simpa [patterns, active, w] using
      doubledBoxNonemptyOriginIncidentSupportPatternOwnerPairs_sum_le_of_forall_le_div_384
        (n := n)
        (F := fun S ew =>
          ∑ m ∈ (Ω.filter active).filter
              (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0),
            doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
              β n v w e0 ew m)
        (target := target) htarget
        (by
          intro S hS ew hew
          exact hpair S (by simpa [patterns] using hS) ew hew)
  simpa [patterns, active, w] using htransport.trans hpairSum

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_activeOriginIncidentSupportPatterns_sum_le_updateSelectedEdgeMultiplicityBudget_sum_of_strictSectorYPredecessor3
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
        (fun S => S.Nonempty),
      ∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => doubledBoxOriginIncidentSupport n m = S)),
        β *
          doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
            e0 m) ≤
      ∑ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
          (fun S => S.Nonempty),
        ∑ ew ∈ S,
          ∑ m ∈
            ((Ω.filter
              (doubledBoxIncrementedFullSourceActive n
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
                e0)).filter
              (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
            β *
              doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand
                β n v
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
                e0 m := by
  classical
  let active :
      (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → Prop :=
    doubledBoxIncrementedFullSourceActive n
      (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
  let F : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ :=
    fun m =>
      β *
        doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β n
          v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m
  let B :
      Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
          (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ :=
    fun _S _ew m => F m
  have htransport :=
    sum_doubledBoxIncrementedFullSourceActive_originIncidentSupportPatternOwnerBudget_le_updateSelectedEdgeMultiplicityBudget_sum_of_nonneg_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) hedge Ω B
      (by
        intro S hS ew hew m hm
        exact mul_nonneg hβ
          (doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_nonneg
            hβ e0 m))
  have hleft :
      (∑ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
          (fun S => S.Nonempty),
        ∑ m ∈
          ((Ω.filter active).filter
            (fun m => doubledBoxOriginIncidentSupport n m = S)),
          F m) =
        ∑ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
          (fun S => S.Nonempty),
          ∑ m ∈
            ((Ω.filter active).filter
              (fun m => doubledBoxOriginIncidentSupport n m = S)),
            match doubledBoxOriginIncidentOwner n m with
            | none => 0
            | some ew => B S ew m := by
    refine Finset.sum_congr rfl ?_
    intro S hS
    have hSnonempty : S.Nonempty := (Finset.mem_filter.mp hS).2
    exact
      (doubledBoxOriginIncidentSupport_filter_sum_ownerIndependentBudget_eq
        (n := n) (Ω.filter active) hSnonempty F).symm
  simpa [active, F, B] using hleft.trans_le htransport

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_activeOriginIncidentSupportPatterns_sum_le_updateSelectedEdgeMultiplicityBudget_sum_of_strictSectorYPredecessor3
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
        (fun S => S.Nonempty),
      ∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => doubledBoxOriginIncidentSupport n m = S)),
        β *
          doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
            e0 m) ≤
      ∑ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
          (fun S => S.Nonempty),
        ∑ ew ∈ S,
          ∑ m ∈
            ((Ω.filter
              (doubledBoxIncrementedFullSourceActive n
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
                e0)).filter
              (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
            β *
              doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand
                β n v
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
                e0 m := by
  classical
  let active :
      (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → Prop :=
    doubledBoxIncrementedFullSourceActive n
      (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
  let F : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ :=
    fun m =>
      β *
        doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand
          β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
          e0 m
  let B :
      Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
          (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ :=
    fun _S _ew m => F m
  have htransport :=
    sum_doubledBoxIncrementedFullSourceActive_originIncidentSupportPatternOwnerBudget_le_updateSelectedEdgeMultiplicityBudget_sum_of_nonneg_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) hedge Ω B
      (by
        intro S hS ew hew m hm
        exact mul_nonneg hβ
          (doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_nonneg
            hβ e0 m))
  have hleft :
      (∑ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
          (fun S => S.Nonempty),
        ∑ m ∈
          ((Ω.filter active).filter
            (fun m => doubledBoxOriginIncidentSupport n m = S)),
          F m) =
        ∑ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
          (fun S => S.Nonempty),
          ∑ m ∈
            ((Ω.filter active).filter
              (fun m => doubledBoxOriginIncidentSupport n m = S)),
            match doubledBoxOriginIncidentOwner n m with
            | none => 0
            | some ew => B S ew m := by
    refine Finset.sum_congr rfl ?_
    intro S hS
    have hSnonempty : S.Nonempty := (Finset.mem_filter.mp hS).2
    exact
      (doubledBoxOriginIncidentSupport_filter_sum_ownerIndependentBudget_eq
        (n := n) (Ω.filter active) hSnonempty F).symm
  simpa [active, F, B] using hleft.trans_le htransport

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_activeOriginIncidentSupportPatterns_sum_le_updateSelectedEdgeMultiplicityBudget_sum_of_strictSectorYPredecessor3
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
        (fun S => S.Nonempty),
      ∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => doubledBoxOriginIncidentSupport n m = S)),
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m) ≤
      ∑ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
          (fun S => S.Nonempty),
        ∑ ew ∈ S,
          ∑ m ∈
            ((Ω.filter
              (doubledBoxIncrementedFullSourceActive n
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
                e0)).filter
              (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
            doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
              m := by
  classical
  let active :
      (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → Prop :=
    doubledBoxIncrementedFullSourceActive n
      (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
  let F : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ :=
    fun m =>
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m
  let B :
      Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
          (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ :=
    fun _S _ew m => F m
  have htransport :=
    sum_doubledBoxIncrementedFullSourceActive_originIncidentSupportPatternOwnerBudget_le_updateSelectedEdgeMultiplicityBudget_sum_of_nonneg_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) hedge Ω B
      (by
        intro S hS ew hew m hm
        exact
          doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_nonneg
            hβ e0 m)
  have hleft :
      (∑ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
          (fun S => S.Nonempty),
        ∑ m ∈
          ((Ω.filter active).filter
            (fun m => doubledBoxOriginIncidentSupport n m = S)),
          F m) =
        ∑ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
          (fun S => S.Nonempty),
          ∑ m ∈
            ((Ω.filter active).filter
              (fun m => doubledBoxOriginIncidentSupport n m = S)),
            match doubledBoxOriginIncidentOwner n m with
            | none => 0
            | some ew => B S ew m := by
    refine Finset.sum_congr rfl ?_
    intro S hS
    have hSnonempty : S.Nonempty := (Finset.mem_filter.mp hS).2
    exact
      (doubledBoxOriginIncidentSupport_filter_sum_ownerIndependentBudget_eq
        (n := n) (Ω.filter active) hSnonempty F).symm
  simpa [active, F, B] using hleft.trans_le htransport

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_activeOriginIncidentSupportPatterns_sum_le_updateSelectedEdgeMultiplicityBudget_sum_of_strictSectorYPredecessor3
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
        (fun S => S.Nonempty),
      ∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => doubledBoxOriginIncidentSupport n m = S)),
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m) ≤
      ∑ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
          (fun S => S.Nonempty),
        ∑ ew ∈ S,
          ∑ m ∈
            ((Ω.filter
              (doubledBoxIncrementedFullSourceActive n
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
                e0)).filter
              (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
            doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n
              v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
              e0 m := by
  classical
  let active :
      (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → Prop :=
    doubledBoxIncrementedFullSourceActive n
      (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
  let F : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ :=
    fun m =>
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m
  let B :
      Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
          (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ :=
    fun _S _ew m => F m
  have htransport :=
    sum_doubledBoxIncrementedFullSourceActive_originIncidentSupportPatternOwnerBudget_le_updateSelectedEdgeMultiplicityBudget_sum_of_nonneg_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) hedge Ω B
      (by
        intro S hS ew hew m hm
        exact
          doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_nonneg
            hβ e0 m)
  have hleft :
      (∑ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
          (fun S => S.Nonempty),
        ∑ m ∈
          ((Ω.filter active).filter
            (fun m => doubledBoxOriginIncidentSupport n m = S)),
          F m) =
        ∑ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
          (fun S => S.Nonempty),
          ∑ m ∈
            ((Ω.filter active).filter
              (fun m => doubledBoxOriginIncidentSupport n m = S)),
            match doubledBoxOriginIncidentOwner n m with
            | none => 0
            | some ew => B S ew m := by
    refine Finset.sum_congr rfl ?_
    intro S hS
    have hSnonempty : S.Nonempty := (Finset.mem_filter.mp hS).2
    exact
      (doubledBoxOriginIncidentSupport_filter_sum_ownerIndependentBudget_eq
        (n := n) (Ω.filter active) hSnonempty F).symm
  simpa [active, F, B] using hleft.trans_le htransport

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge_activeOriginIncidentSupportPatterns_sum_le_updateSelectedEdgeMultiplicityBudget_sum_of_strictSectorYPredecessor3
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
        (fun S => S.Nonempty),
      ∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => doubledBoxOriginIncidentSupport n m = S)),
        match doubledBoxOriginIncidentOwner n m with
        | none => 0
        | some ew =>
            doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge
              β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
              e0 ew m) ≤
      ∑ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
          (fun S => S.Nonempty),
        ∑ ew ∈ S,
          ∑ m ∈
            ((Ω.filter
              (doubledBoxIncrementedFullSourceActive n
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
                e0)).filter
              (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
            doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge
              β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
              e0 ew m := by
  classical
  let B :
      Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
          (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ :=
    fun _S ew m =>
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge β n
        v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 ew m
  simpa [B] using
    sum_doubledBoxIncrementedFullSourceActive_originIncidentSupportPatternOwnerBudget_le_updateSelectedEdgeMultiplicityBudget_sum_of_nonneg_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) hedge Ω B
      (by
        intro S hS ew hew m hm
        exact
          doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge_nonneg
            hβ e0 ew m)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge_activeOriginIncidentSupportPatterns_sum_le_updateSelectedEdgeMultiplicityBudget_sum_of_strictSectorYPredecessor3
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
        (fun S => S.Nonempty),
      ∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => doubledBoxOriginIncidentSupport n m = S)),
        match doubledBoxOriginIncidentOwner n m with
        | none => 0
        | some ew =>
            doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
              β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
              e0 ew m) ≤
      ∑ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
          (fun S => S.Nonempty),
        ∑ ew ∈ S,
          ∑ m ∈
            ((Ω.filter
              (doubledBoxIncrementedFullSourceActive n
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
                e0)).filter
              (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
            doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
              β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
              e0 ew m := by
  classical
  let B :
      Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
          (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ :=
    fun _S ew m =>
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
        β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 ew
        m
  simpa [B] using
    sum_doubledBoxIncrementedFullSourceActive_originIncidentSupportPatternOwnerBudget_le_updateSelectedEdgeMultiplicityBudget_sum_of_nonneg_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) hedge Ω B
      (by
        intro S hS ew hew m hm
        exact
          doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge_nonneg
            hβ e0 ew m)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge_activeOriginIncidentSupportPatterns_sum_le_of_updateSelectedEdgeMultiplicity_pair_sums_le_div_384_strictSectorYPredecessor3
    {β target : ℝ} (hβ : 0 ≤ β) (htarget : 0 ≤ target)
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (hpair :
      ∀ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
          (fun S => S.Nonempty),
        ∀ ew ∈ S,
          (∑ m ∈
            ((Ω.filter
              (doubledBoxIncrementedFullSourceActive n
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
                e0)).filter
              (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
            doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge
              β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
              e0 ew m) ≤ target / 384) :
    (∑ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
        (fun S => S.Nonempty),
      ∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => doubledBoxOriginIncidentSupport n m = S)),
        match doubledBoxOriginIncidentOwner n m with
        | none => 0
        | some ew =>
            doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge
              β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
              e0 ew m) ≤ target := by
  classical
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let active := doubledBoxIncrementedFullSourceActive n w e0
  let patterns : Finset (Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :=
    ((doubledBoxOriginIncidentEdges n).powerset).filter
      (fun S => S.Nonempty)
  have htransport :
      (∑ S ∈ patterns,
        ∑ m ∈ (Ω.filter active).filter
            (fun m => doubledBoxOriginIncidentSupport n m = S),
          match doubledBoxOriginIncidentOwner n m with
          | none => 0
          | some ew =>
              doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge
                β n v w e0 ew m) ≤
        ∑ S ∈ patterns,
          ∑ ew ∈ S,
            ∑ m ∈ (Ω.filter active).filter
                (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0),
              doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge
                β n v w e0 ew m := by
    simpa [patterns, active, w] using
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge_activeOriginIncidentSupportPatterns_sum_le_updateSelectedEdgeMultiplicityBudget_sum_of_strictSectorYPredecessor3
        (β := β) hβ (n := n) (v := v) hvwedge hlt hypos
        (e0 := e0) hedge Ω
  have hpairSum :
      (∑ S ∈ patterns,
        ∑ ew ∈ S,
          ∑ m ∈ (Ω.filter active).filter
              (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0),
            doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge
              β n v w e0 ew m) ≤ target := by
    simpa [patterns, active, w] using
      doubledBoxNonemptyOriginIncidentSupportPatternOwnerPairs_sum_le_of_forall_le_div_384
        (n := n)
        (F := fun S ew =>
          ∑ m ∈ (Ω.filter active).filter
              (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0),
            doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge
              β n v w e0 ew m)
        (target := target) htarget
        (by
          intro S hS ew hew
          exact hpair S (by simpa [patterns] using hS) ew hew)
  simpa [patterns, active, w] using htransport.trans hpairSum

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge_activeOriginIncidentSupportPatterns_sum_le_of_updateSelectedEdgeMultiplicity_pair_sums_le_div_384_strictSectorYPredecessor3
    {β target : ℝ} (hβ : 0 ≤ β) (htarget : 0 ≤ target)
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (hpair :
      ∀ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
          (fun S => S.Nonempty),
        ∀ ew ∈ S,
          (∑ m ∈
            ((Ω.filter
              (doubledBoxIncrementedFullSourceActive n
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
                e0)).filter
              (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
            doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
              β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
              e0 ew m) ≤ target / 384) :
    (∑ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
        (fun S => S.Nonempty),
      ∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => doubledBoxOriginIncidentSupport n m = S)),
        match doubledBoxOriginIncidentOwner n m with
        | none => 0
        | some ew =>
            doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
              β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
              e0 ew m) ≤ target := by
  classical
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let active := doubledBoxIncrementedFullSourceActive n w e0
  let patterns : Finset (Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :=
    ((doubledBoxOriginIncidentEdges n).powerset).filter
      (fun S => S.Nonempty)
  have htransport :
      (∑ S ∈ patterns,
        ∑ m ∈ (Ω.filter active).filter
            (fun m => doubledBoxOriginIncidentSupport n m = S),
          match doubledBoxOriginIncidentOwner n m with
          | none => 0
          | some ew =>
              doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
                β n v w e0 ew m) ≤
        ∑ S ∈ patterns,
          ∑ ew ∈ S,
            ∑ m ∈ (Ω.filter active).filter
                (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0),
              doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
                β n v w e0 ew m := by
    simpa [patterns, active, w] using
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge_activeOriginIncidentSupportPatterns_sum_le_updateSelectedEdgeMultiplicityBudget_sum_of_strictSectorYPredecessor3
        (β := β) hβ (n := n) (v := v) hvwedge hlt hypos
        (e0 := e0) hedge Ω
  have hpairSum :
      (∑ S ∈ patterns,
        ∑ ew ∈ S,
          ∑ m ∈ (Ω.filter active).filter
              (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0),
            doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
              β n v w e0 ew m) ≤ target := by
    simpa [patterns, active, w] using
      doubledBoxNonemptyOriginIncidentSupportPatternOwnerPairs_sum_le_of_forall_le_div_384
        (n := n)
        (F := fun S ew =>
          ∑ m ∈ (Ω.filter active).filter
              (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0),
            doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
              β n v w e0 ew m)
        (target := target) htarget
        (by
          intro S hS ew hew
          exact hpair S (by simpa [patterns] using hS) ew hew)
  simpa [patterns, active, w] using htransport.trans hpairSum

set_option linter.style.longLine false in


theorem sum_finiteSupportExplicitCaseBudgetTotal_strictSectorYActiveOriginIncidentOwnerFilters_le_updateSelectedEdgeMultiplicityFilters_of_nonneg
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    {κ : Type*}
    (caseOf :
      ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → κ)
    (caseSet : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → Finset κ)
    (caseBudget : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → κ → ℝ)
    (hcover :
      ∀ ew ∈ doubledBoxOriginIncidentEdges n,
        ∀ m ∈
          ((Ω.filter
            (doubledBoxIncrementedFullSourceActive n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
            (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
          caseOf ew m ∈ caseSet ew)
    (hnonneg :
      ∀ ew ∈ doubledBoxOriginIncidentEdges n,
        ∀ c ∈ caseSet ew, 0 ≤ caseBudget ew c) :
    (∑ ew ∈ doubledBoxOriginIncidentEdges n,
      finiteSupportExplicitCaseBudgetTotal
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => doubledBoxOriginIncidentOwner n m = some ew))
        (caseOf ew) (caseSet ew) (caseBudget ew)) ≤
      ∑ ew ∈ doubledBoxOriginIncidentEdges n,
        finiteSupportExplicitCaseBudgetTotal
          ((Ω.filter
            (doubledBoxIncrementedFullSourceActive n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
            (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0))
          (caseOf ew) (caseSet ew) (caseBudget ew) := by
  refine Finset.sum_le_sum ?_
  intro ew hew
  exact
    finiteSupportExplicitCaseBudgetTotal_strictSectorYActiveOriginIncidentOwnerFilter_le_updateSelectedEdgeMultiplicityFilter_of_nonneg
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      hedge Ω (caseOf ew) (caseSet ew) (caseBudget ew)
      (hcover ew hew) (hnonneg ew hew)

set_option linter.style.longLine false in


theorem finset_sum_le_of_finiteSupportExplicitCaseBudgetTotal_activeSubset_le_of_relaxed
    {α κ : Type*} (Ω Ωactive : Finset α) (F : α → ℝ)
    (caseOf : α → κ) (caseSet : Finset κ)
    (rowBound relaxedBudget : κ → ℝ) {target : ℝ}
    (hsubset : Ωactive ⊆ Ω)
    (hzero : ∀ a ∈ Ω, a ∉ Ωactive → F a = 0)
    (hcover : ∀ a ∈ Ωactive, caseOf a ∈ caseSet)
    (hpoint : ∀ a ∈ Ωactive, F a ≤ rowBound (caseOf a))
    (hrelax : ∀ c ∈ caseSet, rowBound c ≤ relaxedBudget c)
    (htotal :
      finiteSupportExplicitCaseBudgetTotal Ωactive caseOf caseSet
          relaxedBudget ≤
        target) :
    Finset.sum Ω F ≤ target := by
  have hsum_active :
      Finset.sum Ωactive F = Finset.sum Ω F := by
    exact Finset.sum_subset hsubset hzero
  calc
    Finset.sum Ω F = Finset.sum Ωactive F := hsum_active.symm
    _ ≤ target :=
      finset_sum_le_of_finiteSupportExplicitCaseBudgetTotal_le_of_relaxed
        Ωactive F caseOf caseSet rowBound relaxedBudget hcover hpoint
        hrelax htotal

set_option linter.style.longLine false in


theorem finset_zeroOutside_filter_of_zeroOn_not
    {α γ : Type*} [Zero γ] (Ω : Finset α) (F : α → γ)
    (P : α → Prop) [DecidablePred P]
    (hzero : ∀ a ∈ Ω, ¬ P a → F a = 0) :
    ∀ a ∈ Ω, a ∉ Ω.filter P → F a = 0 := by
  intro a ha hnotActive
  have hnotP : ¬ P a := by
    intro hPa
    exact hnotActive (Finset.mem_filter.mpr ⟨ha, hPa⟩)
  exact hzero a ha hnotP

set_option linter.style.longLine false in


theorem finset_filter_activeSubset_obligations_of_zeroOn_not
    {α γ : Type*} [Zero γ] (Ω : Finset α) (F : α → γ)
    (P : α → Prop) [DecidablePred P]
    (hzero : ∀ a ∈ Ω, ¬ P a → F a = 0) :
    (Ω.filter P ⊆ Ω) ∧
      (∀ a ∈ Ω, a ∉ Ω.filter P → F a = 0) :=
  ⟨Finset.filter_subset P Ω,
    finset_zeroOutside_filter_of_zeroOn_not Ω F P hzero⟩

set_option linter.style.longLine false in


theorem finset_sum_le_of_finiteSupportExplicitCaseBudgetTotal_filter_le_of_relaxed
    {α κ : Type*} (Ω : Finset α) (F : α → ℝ) (P : α → Prop)
    [DecidablePred P] (caseOf : α → κ) (caseSet : Finset κ)
    (rowBound relaxedBudget : κ → ℝ) {target : ℝ}
    (hzero : ∀ a ∈ Ω, ¬ P a → F a = 0)
    (hcover : ∀ a ∈ Ω.filter P, caseOf a ∈ caseSet)
    (hpoint : ∀ a ∈ Ω.filter P, F a ≤ rowBound (caseOf a))
    (hrelax : ∀ c ∈ caseSet, rowBound c ≤ relaxedBudget c)
    (htotal :
      finiteSupportExplicitCaseBudgetTotal (Ω.filter P) caseOf caseSet
          relaxedBudget ≤
        target) :
    Finset.sum Ω F ≤ target := by
  refine
    finset_sum_le_of_finiteSupportExplicitCaseBudgetTotal_activeSubset_le_of_relaxed
      Ω (Ω.filter P) F caseOf caseSet rowBound relaxedBudget
      (Finset.filter_subset P Ω) ?_ hcover hpoint hrelax htotal
  exact finset_zeroOutside_filter_of_zeroOn_not Ω F P hzero

end Exact3D
end StatMech
