import Lemma.Definitions.Def_LanglandsTunnell_SchwartzBruhatSpace
import Lemma.Definitions.Def_RepTheory_MulConvolution
import Mathlib.Topology.Algebra.ContinuousMonoidHom

set_option autoImplicit false

open MeasureTheory Filter Topology

namespace TestFunctionAction

section Transport

variable {X X' : Type*} [TopologicalSpace X] [TopologicalSpace X']

private theorem comp_homeomorph_mem (σ : X ≃ₜ X') {f : X' → ℂ} (hf : f ∈ SchwartzBruhatSpace.testSpace X') :
    f ∘ σ ∈ SchwartzBruhatSpace.testSpace X :=
  ⟨(SchwartzBruhatSpace.isLocallyConstant_of_mem hf).comp_continuous σ.continuous,
    (SchwartzBruhatSpace.hasCompactSupport_of_mem hf).comp_homeomorph σ⟩

end Transport
section Check

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def checkHomeomorph (σ : G ≃ₜ* G) : G ≃ₜ G :=
  (Homeomorph.inv G).trans σ.symm.toHomeomorph

theorem checkHomeomorph_apply (σ : G ≃ₜ* G) (h : G) : checkHomeomorph σ h = σ.symm h⁻¹ := rfl

noncomputable def check (σ : G ≃ₜ* G) :
    SchwartzBruhatSpace.testSpace G →ₗ[ℂ] SchwartzBruhatSpace.testSpace G where
  toFun φ := ⟨fun h => (φ : G → ℂ) (σ.symm h⁻¹),
    comp_homeomorph_mem (checkHomeomorph σ) φ.2⟩
  map_add' φ ψ := by ext h; rfl
  map_smul' c φ := by ext h; rfl

@[simp]
theorem check_apply (σ : G ≃ₜ* G) (φ : SchwartzBruhatSpace.testSpace G) (h : G) :
    (check σ φ : G → ℂ) h = (φ : G → ℂ) (σ.symm h⁻¹) := rfl

end Check

section Convolution

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private theorem exists_mem_nhds_one_right_invariant {φ : G → ℂ} (hlc : IsLocallyConstant φ)
    (hcs : HasCompactSupport φ) :
    ∃ W ∈ 𝓝 (1 : G), ∀ k ∈ W, ∀ g, φ (g * k) = φ g := by
  have hloc : ∀ x : G, ∃ V ∈ 𝓝 x, ∃ W ∈ 𝓝 (1 : G), ∀ g ∈ V, ∀ k ∈ W, φ (g * k) = φ g := by
    intro x
    obtain ⟨U, hUo, hxU, hUc⟩ := hlc.exists_open x
    have hpre : (fun p : G × G => p.1 * p.2) ⁻¹' U ∈ 𝓝 ((x, 1) : G × G) :=
      (hUo.preimage continuous_mul).mem_nhds (by simpa using hxU)
    obtain ⟨V, hV, W, hW, hVW⟩ := mem_nhds_prod_iff.1 hpre
    refine ⟨V, hV, W, hW, fun g hg k hk => ?_⟩
    have h1 : g * k ∈ U := hVW (Set.mk_mem_prod hg hk)
    have h2 : g * 1 ∈ U := hVW (Set.mk_mem_prod hg (mem_of_mem_nhds hW))
    rw [hUc _ h1, ← hUc _ h2, mul_one]
  choose V hV W hW hVW using hloc
  obtain ⟨t, -, ht⟩ := IsCompact.elim_nhds_subcover (s := tsupport φ) hcs V fun x _ => hV x
  set W₀ : Set G := ⋂ x ∈ t, W x with hW₀
  have hW₀n : W₀ ∈ 𝓝 (1 : G) := (biInter_finset_mem t).2 fun x _ => hW x
  have hkey : ∀ k ∈ W₀, ∀ g ∈ tsupport φ, φ (g * k) = φ g := by
    intro k hk g hg
    obtain ⟨x, hxt, hgx⟩ := Set.mem_iUnion₂.1 (ht hg)
    exact hVW x g hgx k (Set.mem_iInter₂.1 hk x hxt)
  refine ⟨W₀ ∩ W₀⁻¹, inter_mem hW₀n (inv_mem_nhds_one G hW₀n), fun k hk g => ?_⟩
  by_cases hg : g ∈ tsupport φ
  · exact hkey k hk.1 g hg
  · by_cases hgk : g * k ∈ tsupport φ
    · have := hkey k⁻¹ (Set.mem_inv.1 hk.2) (g * k) hgk
      rwa [mul_inv_cancel_right, eq_comm] at this
    · rw [image_eq_zero_of_notMem_tsupport hg, image_eq_zero_of_notMem_tsupport hgk]

variable [T2Space G] [MeasurableSpace G]

theorem mulConv_mem_testSpace (μ : Measure G) {φ ψ : G → ℂ}
    (hφ : φ ∈ SchwartzBruhatSpace.testSpace G) (hψ : ψ ∈ SchwartzBruhatSpace.testSpace G) :
    MulConvolution.mulConv μ φ ψ ∈ SchwartzBruhatSpace.testSpace G := by
  refine ⟨MulConvolution.isLocallyConstant_mulConv μ φ ψ ?_,
    MulConvolution.hasCompactSupport_mulConv μ hφ.2 hψ.2⟩
  obtain ⟨U, hU, hUψ⟩ := exists_mem_nhds_one_right_invariant hψ.1 hψ.2
  exact ⟨U, hU, fun u hu x => hUψ u hu x⟩

noncomputable def convolution (μ : Measure G) (φ ψ : SchwartzBruhatSpace.testSpace G) :
    SchwartzBruhatSpace.testSpace G :=
  ⟨MulConvolution.mulConv μ φ ψ, mulConv_mem_testSpace μ φ.2 ψ.2⟩

@[simp]
theorem coe_convolution (μ : Measure G) (φ ψ : SchwartzBruhatSpace.testSpace G) :
    (convolution μ φ ψ : G → ℂ) = MulConvolution.mulConv μ φ ψ := rfl

end Convolution

end TestFunctionAction
