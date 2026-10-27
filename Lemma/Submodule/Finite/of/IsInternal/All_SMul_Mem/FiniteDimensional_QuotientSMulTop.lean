import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.Submodule.Any_And_All_Any_In.of.FiniteDimensional_QuotientSMulTop
import Lemma.Submodule.Any_And_In_Span_InterAndInAndIn_SMulTop.of.All_Any_In.Eq_Top_Span_ImageMkQ.In
import Lemma.Submodule.In_Span_IUnion_Image2SMul.of.In.In_SMulTop
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
Graded Nakayama generators: finite-dimensional quotient implies finite over the graded ring
(atlas lemma_12_3_i_generators).

[lemma_12_3_i_generators](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SyzygiesKoszul.lean)
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
  (hsmul : ∀ (i j : ℕ) (s : S) (m : M), s ∈ 𝒮 j → m ∈ ℳ i → s • m ∈ ℳ (i + j))
  (hfin : FiniteDimensional k (M ⧸ (Ideal.span (⋃ (i : ℕ) (_ : 0 < i), (𝒮 i : Set S))) • (⊤ : Submodule S M))) :
-- imply
  Module.Finite S M := by
-- proof
  set P := ((Ideal.span (⋃ (i : ℕ) (_ : 0 < i), (𝒮 i : Set S))) • (⊤ : Submodule S M))
  obtain ⟨T, hThom, hTspan⟩ :=
    Submodule.Any_And_All_Any_In.of.FiniteDimensional_QuotientSMulTop (𝒮 := 𝒮) (ℳ := ℳ)
      hinter hsmul hfin
  let N := Submodule.span S (T : Set M)
  suffices hN : N = ⊤ by
    rw [Module.finite_def]; exact ⟨T, hN⟩
  rw [eq_top_iff]
  suffices hall : ∀ d, ℳ d ≤ N.restrictScalars k by
    intro m _
    have hint := hinter
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at hint
    have hle : (⨆ d, ℳ d) ≤ N.restrictScalars k := iSup_le hall
    rw [hint.2] at hle
    exact hle Submodule.mem_top
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro m hm
    show m ∈ N
    obtain ⟨v, hv_span, hm_v_d, hm_v_P⟩ :=
      Submodule.Any_And_In_Span_InterAndInAndIn_SMulTop.of.All_Any_In.Eq_Top_Span_ImageMkQ.In
        (𝒮 := 𝒮) (ℳ := ℳ) hinter hsmul hThom hTspan hm
    have hv_N : v ∈ N :=
      Submodule.span_le_restrictScalars k S (↑T : Set M)
        (Submodule.span_mono Set.inter_subset_left hv_span)
    have hm_v_N : m - v ∈ N := by
      have hmem := Submodule.In_Span_IUnion_Image2SMul.of.In.In_SMulTop
        (𝒮 := 𝒮) (ℳ := ℳ) hinter hsmul hm_v_d hm_v_P
      suffices m - v ∈ N.restrictScalars k from this
      apply Submodule.span_le.mpr _ hmem
      intro y hy
      simp only [Set.mem_iUnion, Set.mem_image2, SetLike.mem_coe] at hy
      obtain ⟨j, hj, i, hij, s, hs, m', hm', rfl⟩ := hy
      change s • m' ∈ N
      exact N.smul_mem s (ih i (by omega) hm')
    have : m = v + (m - v) := by abel
    rw [this]
    exact N.add_mem hv_N hm_v_N


-- created on 2026-10-24
