import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
Finite-dimensional quotient by an augmentation-ideal multiple admits a homogeneous spanning set
(atlas exists_homogeneous_span_quotient).

[exists_homogeneous_span_quotient](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SyzygiesKoszul.lean)
-/
@[path]
private lemma main
  [Field k]
  [CommRing S]
  [Algebra k S]
  [AddCommGroup M]
  [Module S M]
  [Module k M]
  [IsScalarTower k S M]
  {𝒮 : ℕ → Submodule k S} [GradedAlgebra 𝒮]
  {ℳ : ℕ → Submodule k M}
-- given
  (hinter : DirectSum.IsInternal ℳ)
  (_ : ∀ (i j : ℕ) (s : S) (m : M), s ∈ 𝒮 j → m ∈ ℳ i → s • m ∈ ℳ (i + j))
  (hfin : FiniteDimensional k (M ⧸ (Ideal.span (⋃ (i : ℕ) (_ : 0 < i), (𝒮 i : Set S))) • (⊤ : Submodule S M))) :
-- imply
  ∃ (T : Finset M), (∀ t ∈ T, ∃ d, t ∈ ℳ d) ∧
    Submodule.span k (((Ideal.span (⋃ (i : ℕ) (_ : 0 < i), (𝒮 i : Set S))) • (⊤ : Submodule S M)).mkQ '' ↑T) = ⊤ := by
-- proof
  classical
  set P := (Ideal.span (⋃ (i : ℕ) (_ : 0 < i), (𝒮 i : Set S))) • (⊤ : Submodule S M)
  set H : Set M := ⋃ d, ↑(ℳ d)
  have hH_span : Submodule.span k H = ⊤ := by
    have hint := hinter
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at hint
    rw [show H = ⋃ d, ↑(ℳ d) from rfl, ← Submodule.iSup_eq_span, hint.2]
  set f := P.mkQ.restrictScalars k
  have hf_surj : Function.Surjective f := Submodule.mkQ_surjective P
  have := hfin
  obtain ⟨S₀, hS₀⟩ := (Module.finite_def.mp inferInstance : (⊤ : Submodule k (M ⧸ P)).FG)
  have hS₀_lift : ∀ q ∈ S₀, ∃ (Tq : Finset M), ↑Tq ⊆ H ∧ q ∈ Submodule.span k (f '' ↑Tq) := by
    intro q _
    obtain ⟨m, hm⟩ := hf_surj q
    have hm_in : m ∈ Submodule.span k H := hH_span ▸ Submodule.mem_top
    obtain ⟨Tm, hTm_sub, hm_mem⟩ := Submodule.mem_span_finite_of_mem_span hm_in
    exact ⟨Tm, hTm_sub, by rw [← hm, Submodule.span_image]; exact Submodule.mem_map_of_mem hm_mem⟩
  choose Tq hTq_sub hTq_mem using hS₀_lift
  set T := S₀.attach.biUnion (fun ⟨q, hq⟩ => Tq q hq)
  refine ⟨T, ?_, ?_⟩
  ·
    intro t ht
    rw [Finset.mem_biUnion] at ht
    obtain ⟨⟨q, hq⟩, _, ht'⟩ := ht
    have : (t : M) ∈ H := hTq_sub q hq (Finset.mem_coe.mpr ht')
    rwa [Set.mem_iUnion] at this
  ·
    rw [eq_top_iff, ← hS₀]
    apply Submodule.span_le.mpr
    intro q hq
    have hq' : q ∈ S₀ := hq
    have hTq_sub_T : (Tq q hq' : Set M) ⊆ (T : Set M) := by
      intro m hm
      show m ∈ T
      rw [Finset.mem_biUnion]
      exact ⟨⟨q, hq'⟩, Finset.mem_attach _ _, hm⟩
    apply Submodule.span_mono _ (hTq_mem q hq')
    intro x ⟨m, hm, hmx⟩
    exact ⟨m, hTq_sub_T hm, hmx⟩


-- created on 2026-10-24
