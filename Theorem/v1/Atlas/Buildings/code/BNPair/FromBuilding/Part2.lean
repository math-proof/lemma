/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/FromBuilding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.Buildings.code.BNPair.Basic.Part2
import Structure.v1.Atlas.Buildings.code.Building.Basic.Part2
import Lemma.Finset.Any_And_All_Eq.of.IsMaximal.In_Faces.In_Apartments
import Lemma.Finset.LabelMap.eq.ImageLabelMap.of.EqLabelMap_Head_ImageLabelMap_Head.IsChainAdjacent.Ne.All_EqLabelMap_ImageLabelMap
import Lemma.Finset.IsMaximalToSimplicialComplex.of.IsMaximal.In_Apartments
import Def.v1.Atlas.Buildings.code.Building.Labels
import Def.v1.Atlas.Buildings.code.Building.RetractionDef
import Structure.v1.Atlas.Buildings.code.Building.ApartmentsCoxeter
import Def.v1.Atlas.Buildings.code.BNPair.FromBuilding.Part3
set_option linter.unusedSectionVars false

variable {V : Type*} [DecidableEq V]


namespace BNPairFromBuildingData

variable {V : Type*} [DecidableEq V]
  {G : Type*} [Group G]
  {b : Building V}
  {ct : Building.CoxeterTypeOfBuilding b}
  (data : BNPairFromBuildingData G b ct)

/-- Surjectivity of $\pi$: every $w \in W$ is realized by some $n \in N$. Uses strong
transitivity of $G$ on apartment-chamber pairs to find an element moving $C_0$ to the
chamber corresponding to $w$ in $A_0$. -/
theorem π_surj : Function.Surjective data.π := by
  intro w

  obtain ⟨Cw, hCw_max, hCw_φ⟩ := data.φ_surj w

  obtain ⟨g, hg_apt, hg_ch⟩ := data.strongly_transitive data.A₀ data.A₀ data.C₀ Cw
    data.hA₀ data.hA₀ data.hC₀_max_A₀ hCw_max

  have hgN : g ∈ data.N := hg_apt

  exact ⟨⟨g, hgN⟩, by simp only [π, MonoidHom.coe_mk, OneHom.coe_mk, πFun, hg_ch, hCw_φ]⟩

/-- **Kernel of $\pi$ equals $T$.** $\pi(n) = 1$ iff $n$ fixes $C_0$ (forwards: $\varphi$ is
injective on chambers, so $n \cdot C_0 = C_0$; backwards: $T = B \cap N$ fixes $C_0$ and
$\varphi(C_0) = 1$). -/
theorem π_ker (n : data.N) : data.π n = 1 ↔ (n : G) ∈ data.T := by
  constructor
  · intro h

    have h1 : data.φ (data.act.smulFace (n : G) data.C₀) = data.φ data.C₀ := by
      simp only [π, MonoidHom.coe_mk, OneHom.coe_mk, πFun] at h
      rw [h, data.φ_base]

    have hn : data.act.smulFaces (n : G) data.A₀.faces = data.A₀.faces := n.2
    have hmax : data.A₀.IsMaximal (data.act.smulFace (n : G) data.C₀) :=
      data.smul_preserves_apt_max _ hn _ data.hC₀_max_A₀

    have h2 : data.act.smulFace (n : G) data.C₀ = data.C₀ :=
      data.φ_inj _ hmax _ data.hC₀_max_A₀ h1

    show (n : G) ∈ data.act.chamberStabilizer data.C₀ ⊓ data.act.apartmentStabilizer data.A₀
    exact ⟨h2, n.2⟩
  · intro h

    obtain ⟨hB, _⟩ := h
    simp only [π, MonoidHom.coe_mk, OneHom.coe_mk, πFun]

    rw [hB, data.φ_base]

/-- $B$ and $N$ generate $G$: a direct consequence of the Bruhat-style decomposition
$G = B \cdot N \cdot B$ supplied by `bruhat_decomp`. -/
theorem generates : Subgroup.closure ((data.B : Set G) ∪ (data.N : Set G)) = ⊤ := by
  rw [eq_top_iff]
  intro g _
  obtain ⟨b₁, hb₁, n, hn, b₂, hb₂, hg⟩ := data.bruhat_decomp g
  rw [hg]
  have hb₁_mem : b₁ ∈ Subgroup.closure ((data.B : Set G) ∪ (data.N : Set G)) :=
    Subgroup.subset_closure (Set.mem_union_left _ hb₁)
  have hn_mem : n ∈ Subgroup.closure ((data.B : Set G) ∪ (data.N : Set G)) :=
    Subgroup.subset_closure (Set.mem_union_right _ hn)
  have hb₂_mem : b₂ ∈ Subgroup.closure ((data.B : Set G) ∪ (data.N : Set G)) :=
    Subgroup.subset_closure (Set.mem_union_left _ hb₂)
  exact mul_mem (mul_mem hb₁_mem hn_mem) hb₂_mem

end BNPairFromBuildingData
