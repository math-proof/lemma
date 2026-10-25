/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/ParabolicDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.Buildings.code.BNPair.Basic.Part2
import Mathlib.Tactic.Group
import Structure.v1.Atlas.Buildings.code.BNPair.ParabolicDefs
set_option linter.unusedSectionVars false

variable {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}


namespace BNPair

/-- Every Bruhat cell $BwB$ is nonempty: pick any $N$-lift $n$ of $w$ to witness it. -/
theorem exists_mem_bruhatCell (bp : BNPair G M) (w : M.Group) :
    (bp.bruhatCell w).Nonempty := by
  obtain ⟨n, rfl⟩ := bp.π_surj w
  exact ⟨(n : G), ⟨1, bp.B.one_mem⟩, n, ⟨1, bp.B.one_mem⟩, rfl, by simp⟩

/-- If $g \in gPg^{-1}$ then in fact $g \in P$: cancelling the conjugation gives $p = g$. -/
theorem mem_conj_image_self (P : Set G) (g : G)
    (h : g ∈ (fun x => g * x * g⁻¹) '' P) : g ∈ P := by
  obtain ⟨p, hp, hgp⟩ := h
  have hgp' : g * p * g⁻¹ = g := hgp
  have hp_eq : p = g := by
    have h1 : g * p = g * g := by
      calc g * p = g * p * g⁻¹ * g := by group
           _ = g * g := by rw [hgp']
    exact mul_left_cancel h1
  rw [← hp_eq]; exact hp

/-- If $P$ is closed under multiplication and inverse, $g \in Q$, and $gPg^{-1} = Q$,
then $P = Q$: the conjugator $g$ already lies in $P$, so conjugation by $g$ is an
automorphism of $P$. -/
theorem conj_image_eq (P Q : Set G) (g : G)
    (hgQ : g ∈ Q)
    (hP_mul : ∀ x y, x ∈ P → y ∈ P → x * y ∈ P)
    (hP_inv : ∀ x, x ∈ P → x⁻¹ ∈ P)
    (hconj : (fun x => g * x * g⁻¹) '' P = Q) :
    P = Q := by
  have hgP : g ∈ P := mem_conj_image_self P g (hconj ▸ hgQ)
  have hgP_inv : g⁻¹ ∈ P := hP_inv _ hgP
  have self_conj : (fun x => g * x * g⁻¹) '' P = P := by
    ext x; simp only [Set.mem_image]
    constructor
    · rintro ⟨p, hp, hpx⟩
      have hpx' : g * p * g⁻¹ = x := hpx
      rw [← hpx']
      exact hP_mul _ _ (hP_mul _ _ hgP hp) hgP_inv
    · intro hx
      refine ⟨g⁻¹ * x * g, hP_mul _ _ (hP_mul _ _ hgP_inv hx) hgP, ?_⟩
      show g * (g⁻¹ * x * g) * g⁻¹ = x
      group
  rw [self_conj] at hconj
  exact hconj

/-- **Injectivity of the standard parabolics.** Distinct subsets $S_1, S_2 \subseteq S$
give distinct parabolics: if $P_{S_1} = P_{S_2}$ then $S_1 = S_2$.
Equivalently, the map $S' \mapsto P_{S'}$ from subsets of $S$ to subgroups of $G$
containing $B$ is injective. -/
theorem standardParabolicInjective (bp : BNPair G M) (bd : BruhatProperties bp)
    (S₁ S₂ : Set B_idx)
    (h : bp.standardParabolic S₁ = bp.standardParabolic S₂) : S₁ = S₂ := by
  apply bd.parabolicW_injective
  rw [Subgroup.ext_iff]
  intro w₀
  constructor <;> intro hw₀
  · obtain ⟨g, hg⟩ := exists_mem_bruhatCell bp w₀
    have g_in : g ∈ bp.standardParabolic S₂ :=
      h ▸ Set.mem_iUnion₂.mpr ⟨w₀, hw₀, hg⟩
    obtain ⟨u, hu, g_in_Bu⟩ := Set.mem_iUnion₂.mp g_in
    exact bd.cell_disjoint w₀ u ⟨g, hg, g_in_Bu⟩ ▸ hu
  · obtain ⟨g, hg⟩ := exists_mem_bruhatCell bp w₀
    have g_in : g ∈ bp.standardParabolic S₁ :=
      h ▸ Set.mem_iUnion₂.mpr ⟨w₀, hw₀, hg⟩
    obtain ⟨u, hu, g_in_Bu⟩ := Set.mem_iUnion₂.mp g_in
    exact bd.cell_disjoint w₀ u ⟨g, hg, g_in_Bu⟩ ▸ hu

/-- **Parabolics are subgroups.** Each standard parabolic $P_{S'} = BW_{S'}B$ contains
the identity and is closed under multiplication and inverses, so it is a subgroup of $G$. -/
theorem parabolicsAreSubgroups (bp : BNPair G M) (bd : BruhatProperties bp)
    (S' : Set B_idx) :
    (1 : G) ∈ bp.standardParabolic S' ∧
    (∀ x y, x ∈ bp.standardParabolic S' → y ∈ bp.standardParabolic S' →
      x * y ∈ bp.standardParabolic S') ∧
    (∀ x, x ∈ bp.standardParabolic S' → x⁻¹ ∈ bp.standardParabolic S') := by
  refine ⟨?_, ?_, ?_⟩
  · rw [standardParabolic, Set.mem_iUnion₂]
    refine ⟨1, (bp.parabolicSubgroupW S').one_mem, ?_⟩
    obtain ⟨n₀, hn₀⟩ := bp.π_surj (1 : M.Group)
    have n₀_in_T : (n₀ : G) ∈ bp.T := (bp.π_ker n₀).mp hn₀
    have n₀_in_B : (n₀ : G) ∈ bp.B := by
      rw [bp.T_eq] at n₀_in_T; exact (Subgroup.mem_inf.mp n₀_in_T).1
    exact ⟨⟨(↑n₀)⁻¹, bp.B.inv_mem n₀_in_B⟩, n₀, ⟨1, bp.B.one_mem⟩, hn₀, by simp⟩
  · intro x y hx hy
    rw [standardParabolic, Set.mem_iUnion₂] at hx hy ⊢
    obtain ⟨w₁, hw₁, hxw₁⟩ := hx
    obtain ⟨w₂, hw₂, hyw₂⟩ := hy
    obtain ⟨u, hu, hxyu⟩ :=
      bd.cell_mul_in_parabolic S' w₁ w₂ hw₁ hw₂ x y hxw₁ hyw₂
    exact ⟨u, hu, hxyu⟩
  · intro x hx
    rw [standardParabolic, Set.mem_iUnion₂] at hx ⊢
    obtain ⟨w, hw, hxw⟩ := hx
    exact ⟨w⁻¹, (bp.parabolicSubgroupW S').inv_mem hw, bd.cell_inv w x hxw⟩

end BNPair
