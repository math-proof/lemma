/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/BuildingsFromBNPairs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.Buildings.code.BNPair.Basic.Part2
import Def.v1.Atlas.Buildings.code.BNPair.ParabolicDefs.Part2
import Lemma.Nat.NonemptyBruhatCell
import Lemma.Set.All_In_StandardParabolic
import Lemma.Nat.B.le.Closure_BruhatCell
import Theorem.v1.Atlas.Buildings.code.BNPair.ConjugatorProof
import Def.v1.Atlas.Buildings.code.BNPair.NormalizerParabolicProof
import Mathlib.Tactic.Group
import Def.v1.Atlas.Buildings.code.BNPair.BuildingsFromBNPairs
set_option linter.unusedSectionVars false

variable {B_idx : Type*} [DecidableEq B_idx]


namespace BNPair

variable {G : Type*} [Group G] {M : CoxeterMatrix B_idx}

/-- If $g P_{S_1} \subseteq h P_{S_2}$ then $g \in h P_{S_2}$, witnessed by some $q \in P_{S_2}$. -/
theorem coset_element_in_target (bp : BNPair G M)
    (bd : BruhatProperties bp) (g h : G) (S₁ S₂ : Set B_idx)
    (hcontain : bp.leftCoset g S₁ ⊆ bp.leftCoset h S₂) :
    ∃ q : G, q ∈ bp.standardParabolic S₂ ∧ g = h * q := by
  have h1 : (1 : G) ∈ bp.standardParabolic S₁ := (parabolicsAreSubgroups bp bd S₁).1
  have hg_mem : g * 1 ∈ bp.leftCoset g S₁ := by
    show g * 1 ∈ (fun x => g * x) '' bp.standardParabolic S₁
    exact Set.mem_image_of_mem _ h1
  have hg_in := hcontain (by rwa [mul_one] at hg_mem)
  obtain ⟨q, hq, hgq⟩ := hg_in
  exact ⟨q, hq, by simpa using hgq.symm⟩

/-- Coset inclusion forces inclusion of the underlying parabolics: $g P_{S_1} \subseteq h P_{S_2}$
implies $P_{S_1} \subseteq P_{S_2}$. -/
theorem coset_inclusion_implies_subgroup_inclusion (bp : BNPair G M)
    (bd : BruhatProperties bp) (g h : G) (S₁ S₂ : Set B_idx)
    (hcontain : bp.leftCoset g S₁ ⊆ bp.leftCoset h S₂) :
    bp.standardParabolic S₁ ⊆ bp.standardParabolic S₂ := by
  obtain ⟨q, hq, hg_eq⟩ := coset_element_in_target bp bd g h S₁ S₂ hcontain
  intro x hx

  have : g * x ∈ bp.leftCoset g S₁ := Set.mem_image_of_mem _ hx
  have hgx_in := hcontain this
  obtain ⟨z, hz, hgxz⟩ := hgx_in


  have hgxz' : h * z = g * x := by simpa using hgxz
  have hqx : q * x = z := by
    have : h * q * x = h * z := by rw [← hg_eq, hgxz']
    have : h * (q * x) = h * z := by rwa [mul_assoc] at this
    exact mul_left_cancel this
  have : x = q⁻¹ * z := by rw [← hqx]; group
  rw [this]
  exact (parabolicsAreSubgroups bp bd S₂).2.1 _ _
    ((parabolicsAreSubgroups bp bd S₂).2.2 _ hq) hz

/-- The conjugation map descends to cosets: if $g P_{S'} = h P_{S'}$ then $g P_{S'} g^{-1} = h P_{S'} h^{-1}$. -/
theorem conjugation_well_defined (bp : BNPair G M)
    (bd : BruhatProperties bp) (g h : G) (S' : Set B_idx)
    (heq : bp.leftCoset g S' = bp.leftCoset h S') :
    bp.conjugateParabolic g S' = bp.conjugateParabolic h S' := by

  have h1_mem := (parabolicsAreSubgroups bp bd S').1
  have hg_mem : g ∈ bp.leftCoset h S' := by
    rw [← heq]
    show g ∈ (fun x => g * x) '' bp.standardParabolic S'
    exact ⟨1, h1_mem, mul_one g⟩
  obtain ⟨p₀, hp₀, hg_eq'⟩ := hg_mem
  have hg_eq : g = h * p₀ := by simpa using hg_eq'.symm
  unfold conjugateParabolic; ext y; simp only [Set.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨p₀ * x * p₀⁻¹, (parabolicsAreSubgroups bp bd S').2.1 _ _
      ((parabolicsAreSubgroups bp bd S').2.1 _ _ hp₀ hx)
      ((parabolicsAreSubgroups bp bd S').2.2 _ hp₀), ?_⟩
    show h * (p₀ * x * p₀⁻¹) * h⁻¹ = g * x * g⁻¹
    rw [hg_eq]; group
  · rintro ⟨x, hx, rfl⟩
    refine ⟨p₀⁻¹ * x * p₀, (parabolicsAreSubgroups bp bd S').2.1 _ _
      ((parabolicsAreSubgroups bp bd S').2.1 _ _
        ((parabolicsAreSubgroups bp bd S').2.2 _ hp₀) hx) hp₀, ?_⟩
    show g * (p₀⁻¹ * x * p₀) * g⁻¹ = h * x * h⁻¹
    rw [hg_eq]; group

/-- Conjugation respects the inclusion order on coset facets: $g P_{S_1} \subseteq h P_{S_2}$
implies $g P_{S_1} g^{-1} \subseteq h P_{S_2} h^{-1}$. -/
theorem conjugation_mono (bp : BNPair G M)
    (bd : BruhatProperties bp) (g h : G) (S₁ S₂ : Set B_idx)
    (hcontain : bp.leftCoset g S₁ ⊆ bp.leftCoset h S₂) :
    bp.conjugateParabolic g S₁ ⊆ bp.conjugateParabolic h S₂ := by
  obtain ⟨q, hq, hg_eq⟩ := coset_element_in_target bp bd g h S₁ S₂ hcontain
  have hsub := coset_inclusion_implies_subgroup_inclusion bp bd g h S₁ S₂ hcontain
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy
  refine ⟨q * x * q⁻¹, (parabolicsAreSubgroups bp bd S₂).2.1 _ _
    ((parabolicsAreSubgroups bp bd S₂).2.1 _ _ hq (hsub hx))
    ((parabolicsAreSubgroups bp bd S₂).2.2 _ hq), ?_⟩
  show h * (q * x * q⁻¹) * h⁻¹ = g * x * g⁻¹
  rw [hg_eq]; group

/-- The *type* (parabolic-index $S'$) of a coset facet is well-defined: if $g P_{S_1} = h P_{S_2}$
as subsets of $G$, then $S_1 = S_2$. This makes the building's labelling unambiguous. -/
theorem labelling_well_defined (bp : BNPair G M)
    (bd : BruhatProperties bp) (g h : G) (S₁ S₂ : Set B_idx)
    (heq : bp.leftCoset g S₁ = bp.leftCoset h S₂) :
    S₁ = S₂ := by
  have h12 := coset_inclusion_implies_subgroup_inclusion bp bd g h S₁ S₂ heq.le
  have h21 := coset_inclusion_implies_subgroup_inclusion bp bd h g S₂ S₁ heq.ge
  exact standardParabolicInjective bp bd S₁ S₂ (Set.Subset.antisymm h12 h21)

end BNPair
