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
import Def.v1.Atlas.Buildings.code.BNPair.BuildingsFromBNPairs.Part2
set_option linter.unusedSectionVars false

variable {B_idx : Type*} [DecidableEq B_idx]


namespace BNPair

variable {G : Type*} [Group G] {M : CoxeterMatrix B_idx}

/-- $B$ is contained in every standard parabolic $P_{S'}$. -/
theorem B_mem_standardParabolic (bp : BNPair G M) (S' : Set B_idx)
    (b : G) (hb : b ∈ bp.B) :
    b ∈ bp.standardParabolic S' := by
  rw [standardParabolic, Set.mem_iUnion₂]
  exact ⟨1, (bp.parabolicSubgroupW S').one_mem,
    ⟨⟨b, hb⟩, ⟨1, bp.N.one_mem⟩, ⟨1, bp.B.one_mem⟩,
      bp.π.map_one, by simp⟩⟩

/-- If conjugation by $g$ sends $P_{S_1}$ into $P_{S_2}$, then $g$ itself lies in $P_{S_2}$.
A self-normalization property of standard parabolics. -/
theorem conjugator_in_target_of_subset {B_idx : Type*} [DecidableEq B_idx]
    {G : Type*} [Group G] {M : CoxeterMatrix B_idx}
    (bp : BNPair G M) (bd : BruhatProperties bp)
    (ax : BNPairAxioms bp)
    (S₁ S₂ : Set B_idx) (g : G)
    (hsub : (fun x => g * x * g⁻¹) '' bp.standardParabolic S₁ ⊆
      bp.standardParabolic S₂) :
    g ∈ bp.standardParabolic S₂ := by

  let PS₂ := bp.standardParabolic S₂
  let pAS₂ := parabolicsAreSubgroups bp bd S₂

  let Q : Subgroup G :=
  { carrier := PS₂
    mul_mem' := fun hx hy => pAS₂.2.1 _ _ hx hy
    one_mem' := pAS₂.1
    inv_mem' := fun hx => pAS₂.2.2 _ hx }
  have hBQ : bp.B ≤ Q := B_mem_standardParabolic bp S₂


  have hgBg_sub : ∀ b ∈ bp.B, g * b * g⁻¹ ∈ PS₂ := by
    intro b hb
    have hb_PS1 : b ∈ bp.standardParabolic S₁ :=
      B_mem_standardParabolic bp S₁ b hb
    exact hsub ⟨b, hb_PS1, rfl⟩

  obtain ⟨w, hwg⟩ := bd.cell_cover g

  obtain ⟨⟨b₁, hb₁⟩, n, ⟨b₂, hb₂⟩, hπ, hg_eq⟩ := hwg

  have hn_conj : ∀ b' ∈ bp.B, (n : G) * b' * (n : G)⁻¹ ∈ (Q : Set G) := by
    intro b' hb'
    have hb'' : (b₂ : G)⁻¹ * b' * b₂ ∈ bp.B :=
      bp.B.mul_mem (bp.B.mul_mem (bp.B.inv_mem hb₂) hb') hb₂
    have hgconj : g * ((b₂ : G)⁻¹ * b' * b₂) * g⁻¹ ∈ PS₂ := hgBg_sub _ hb''
    have heq : g * ((b₂ : G)⁻¹ * b' * b₂) * g⁻¹ =
        (b₁ : G) * ((n : G) * b' * (n : G)⁻¹) * (b₁ : G)⁻¹ := by
      rw [hg_eq]; group
    rw [heq] at hgconj
    have hb₁_Q : b₁ ∈ (Q : Set G) := hBQ hb₁
    have hb₁_inv_Q : b₁⁻¹ ∈ (Q : Set G) := Q.inv_mem hb₁_Q
    have key : (n : G) * b' * (n : G)⁻¹ =
        b₁⁻¹ * (b₁ * ((n : G) * b' * (n : G)⁻¹) * b₁⁻¹) * b₁ := by group
    rw [key]
    exact Q.mul_mem (Q.mul_mem hb₁_inv_Q hgconj) hb₁_Q

  have hBwB_sub : bp.bruhatCell w ⊆ PS₂ :=
    NormalizerParabolic.bruhatCell_sub_of_conj bp ax Q hBQ w n hπ hn_conj

  exact hBwB_sub ⟨⟨b₁, hb₁⟩, n, ⟨b₂, hb₂⟩, hπ, hg_eq⟩

/-- From $g P_{S_1} g^{-1} \subseteq P_{S_2}$ deduce the direct inclusion $P_{S_1} \subseteq P_{S_2}$. -/
theorem subgroup_inclusion_of_conj_inclusion (bp : BNPair G M)
    (bd : BruhatProperties bp) (ax : BNPairAxioms bp)
    (S₁ S₂ : Set B_idx) (g : G)
    (hsub : (fun x => g * x * g⁻¹) '' bp.standardParabolic S₁ ⊆
      bp.standardParabolic S₂) :
    bp.standardParabolic S₁ ⊆ bp.standardParabolic S₂ := by
  have hg_mem := conjugator_in_target_of_subset bp bd ax S₁ S₂ g hsub
  intro x hx

  have hgxg : g * x * g⁻¹ ∈ bp.standardParabolic S₂ :=
    hsub ⟨x, hx, rfl⟩

  have hx_eq : x = g⁻¹ * (g * x * g⁻¹) * g := by group
  rw [hx_eq]
  exact (parabolicsAreSubgroups bp bd S₂).2.1 _ _
    ((parabolicsAreSubgroups bp bd S₂).2.1 _ _
      ((parabolicsAreSubgroups bp bd S₂).2.2 _ hg_mem) hgxg)
    hg_mem

/-- Reverse direction of `conjugation_mono`: inclusion of conjugate parabolics
$g P_{S_1} g^{-1} \subseteq h P_{S_2} h^{-1}$ implies inclusion of cosets $g P_{S_1} \subseteq h P_{S_2}$. -/
theorem conjugation_reflects_order (bp : BNPair G M)
    (bd : BruhatProperties bp) (ax : BNPairAxioms bp)
    (g h : G) (S₁ S₂ : Set B_idx)
    (hcontain : bp.conjugateParabolic g S₁ ⊆ bp.conjugateParabolic h S₂) :
    bp.leftCoset g S₁ ⊆ bp.leftCoset h S₂ := by

  have hsub : (fun x => (h⁻¹ * g) * x * (h⁻¹ * g)⁻¹) '' bp.standardParabolic S₁ ⊆
      bp.standardParabolic S₂ := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy

    show h⁻¹ * g * x * (h⁻¹ * g)⁻¹ ∈ bp.standardParabolic S₂

    have hgxg : g * x * g⁻¹ ∈ bp.conjugateParabolic g S₁ :=
      ⟨x, hx, rfl⟩
    have hgxg_in := hcontain hgxg

    obtain ⟨z, hz, hzq⟩ := hgxg_in


    have heq : h⁻¹ * g * x * (h⁻¹ * g)⁻¹ = z := by
      have hzq' : h * z * h⁻¹ = g * x * g⁻¹ := hzq
      calc h⁻¹ * g * x * (h⁻¹ * g)⁻¹
          = h⁻¹ * (g * x * g⁻¹) * h := by group
        _ = h⁻¹ * (h * z * h⁻¹) * h := by rw [hzq']
        _ = z := by group
    rw [heq]; exact hz

  set a := h⁻¹ * g with ha_def
  have ha_mem := conjugator_in_target_of_subset bp bd ax S₁ S₂ a hsub
  have hP_sub := subgroup_inclusion_of_conj_inclusion bp bd ax S₁ S₂ a hsub

  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy

  show g * x ∈ bp.leftCoset h S₂
  refine ⟨a * x, ?_, ?_⟩
  ·
    exact (parabolicsAreSubgroups bp bd S₂).2.1 _ _ ha_mem (hP_sub hx)
  ·
    show h * (a * x) = g * x
    simp [ha_def]; group

end BNPair
