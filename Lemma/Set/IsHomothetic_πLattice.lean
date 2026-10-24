import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.Building.AffineSLV
open AffineBuildingSLV AffineBuildingSLVAxioms


namespace AffineBuildingSLV

variable (C : DVRContext)
/--
[πLattice_homothetic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLV.lean)
-/
@[path]
factor $\pi$. -/
lemma πLattice_homothetic (hπ : C.embed C.uniformizer ≠ 0)
  (Λ : DVRContext.OLattice C) :
  IsHomothetic C (πLattice C hπ Λ) Λ :=
  ⟨C.embed C.uniformizer, hπ, rfl⟩

end AffineBuildingSLV

namespace AffineBuildingSLV

/--
[OLattice.incident_symm_lattice](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLV.lean)
-/
@[path]
lemma OLattice.incident_symm_lattice
  {C : DVRContext}
  {x y : DVRContext.OLattice C}
-- given
  (hπ : C.embed C.uniformizer ≠ 0)
  (h : OLattice.IsIncident C x y) :
-- imply
  OLattice.IsIncident C y (πLattice C hπ x) := by
-- proof
  obtain ⟨hyx, hπxy⟩ := h
  exact ⟨fun v ⟨w, hw, hv⟩ => hv ▸ hπxy w hw,
    fun v hv => ⟨v, hyx hv, rfl⟩⟩

end AffineBuildingSLV

namespace AffineBuildingSLVAxioms

/--
[strong_transitivity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLV.lean)
-/
@[path]
lemma strong_transitivity
  {C : DVRContext}
  {σ : AffineBuildingSLV.Simplex C}
  {F₀ : AffineBuildingSLV.Frame C}
  {τ : AffineBuildingSLV.Simplex C}
-- given
  (common_apt : ∀ (σ τ : AffineBuildingSLV.Simplex C), σ.IsMaximal C → τ.IsMaximal C → ∃ F, σ ∈ AffineBuildingSLV.Apartment C F ∧ τ ∈ AffineBuildingSLV.Apartment C F)
  (apt_iso : ∀ (F₁ F₂ : AffineBuildingSLV.Frame C) (σ : AffineBuildingSLV.Simplex C), σ ∈ AffineBuildingSLV.Apartment C F₁ → σ ∈ AffineBuildingSLV.Apartment C F₂ → ∃ φ : AffineBuildingSLV.Simplex C → AffineBuildingSLV.Simplex C, (∀ τ ∈ AffineBuildingSLV.Apartment C F₁, φ τ ∈ AffineBuildingSLV.Apartment C F₂) ∧ φ σ = σ)
  (hσ : σ.IsMaximal C)
  (hσF₀ : σ ∈ AffineBuildingSLV.Apartment C F₀)
  (hτ : τ.IsMaximal C) :
-- imply
  ∃ φ : AffineBuildingSLV.Simplex C → AffineBuildingSLV.Simplex C, φ τ ∈ AffineBuildingSLV.Apartment C F₀ ∧ φ σ = σ := by
-- proof
  obtain ⟨F, hσF, hτF⟩ := common_apt σ τ hσ hτ
  obtain ⟨φ, hφ_mem, hφ_fix⟩ := apt_iso F F₀ σ hσF hσF₀
  exact ⟨φ, hφ_mem τ hτF, hφ_fix⟩

end AffineBuildingSLVAxioms

namespace AffineBuildingSLVAxioms

/--
[congruent_to_identity_is_upper_tri](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLV.lean)
-/
@[path]
lemma congruent_to_identity_is_upper_tri
  {C : DVRContext}
  {g : Fin C.n → Fin C.n → C.𝔬}
-- given
  (hg : IsCongruentToIdentityModM C g) :
-- imply
  IsUpperTriangularModM C g := by
-- proof
  intro i j hij
  obtain ⟨h, hh⟩ := hg i j
  have hne : i ≠ j := Fin.ne_of_gt hij
  simp only [if_neg hne] at hh
  rw [sub_zero] at hh
  exact ⟨h, hh⟩

end AffineBuildingSLVAxioms

namespace AffineBuildingSLVAxioms

/--
[open_plus_decomp_implies_closed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLV.lean)
-/
@[path]
lemma open_plus_decomp_implies_closed
  {C : DVRContext}
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

end AffineBuildingSLVAxioms

namespace AffineBuildingSLVAxioms

/--
[closed_in_compact_is_compact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLV.lean)
-/
@[path]
lemma closed_in_compact_is_compact
  {C : DVRContext}
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

end AffineBuildingSLVAxioms


-- created on 2026-10-23
