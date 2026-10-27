import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.Buildings.code.Building.AffineIsometryAxiomsAction
open AffineIsometryBuilding DVRContext


open-cell partition is closed, because its complement is the open union of


/--
[isometry_congruent_to_identity_is_upper_tri](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineIsometryAxiomsAction.lean)
-/
@[path]
private lemma main
  {C : DVRContext}
  {g : Fin C.n → Fin C.n → C.𝔬}
-- given
  (hg : IsCongruentToIdentity_Isometry C g) :
-- imply
  IsUpperTriangularModM_Isometry C g := by
-- proof
  intro i j hij
  obtain ⟨h, hh⟩ := hg i j
  have hne : i ≠ j := Fin.ne_of_gt hij
  simp only [if_neg hne] at hh
  rw [sub_zero] at hh
  exact ⟨h, hh⟩

/--
[open_plus_decomp_closed_isometry](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineIsometryAxiomsAction.lean)
-/
private lemma open_plus_decomp_closed_isometry
  [TopologicalSpace α]
  {B : Set α}
-- given
  (_hopen : IsOpen B)
  (hdecomp : ∃ (I : Type*) (cells : I → Set α), (∀ i, IsOpen (cells i)) ∧ Set.univ = ⋃ i, cells i ∧ (∀ i j, i ≠ j → Disjoint (cells i) (cells j)) ∧ ∃ i₀, cells i₀ = B) :
-- imply
  IsClosed B := by
-- proof
  obtain ⟨I, cells, hcells_open, hcover, hdisj, i₀, hi₀⟩ := hdecomp
  rw [← isOpen_compl_iff]
  have hBc : Bᶜ = ⋃ (i : {i // i ≠ i₀}), cells i.1 := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion]
    constructor
    · intro hxB
      have hx_univ : x ∈ Set.univ := Set.mem_univ x
      rw [hcover] at hx_univ
      simp only [Set.mem_iUnion] at hx_univ
      obtain ⟨i, hi⟩ := hx_univ
      have hne : i ≠ i₀ := fun heq => hxB (hi₀ ▸ heq ▸ hi)
      exact ⟨⟨i, hne⟩, hi⟩
    · intro ⟨⟨i, hne⟩, hxi⟩ hxB
      rw [← hi₀] at hxB
      exact Set.disjoint_left.mp (hdisj i i₀ hne) hxi hxB
  rw [hBc]
  exact isOpen_iUnion (fun ⟨i, _⟩ => hcells_open i)

/--
[closed_in_compact_isometry](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineIsometryAxiomsAction.lean)
-/
private lemma closed_in_compact_isometry
  [TopologicalSpace α]
  {B K : Set α}
-- given
  (hB_closed : IsClosed B)
  (hBK : B ⊆ K)
  (hK_compact : IsCompact K) :
-- imply
  IsCompact B :=
-- proof
  hK_compact.of_isClosed_subset hB_closed hBK

/--
[maximal_apartment_system](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineIsometryAxiomsAction.lean)
-/
private lemma maximal_apartment_system
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  {Δ : ThickBuildingData G X}
  {𝒜 : Set (Set X)}
-- given
  (h𝒜_stable : ∀ g : G, ∀ A ∈ 𝒜, (fun x => Δ.act g x) '' A ∈ 𝒜)
  (hA₀_in_𝒜 : Δ.A₀ ∈ 𝒜)
  (h𝒜_sub_max : 𝒜 ⊆ Δ.maxAptSystem) :
-- imply
  𝒜 = Δ.maxAptSystem :=
-- proof
  G_stable_is_maximal_apartment_system Δ 𝒜 h𝒜_stable hA₀_in_𝒜 h𝒜_sub_max


-- created on 2026-10-23
-- updated on 2026-10-26
