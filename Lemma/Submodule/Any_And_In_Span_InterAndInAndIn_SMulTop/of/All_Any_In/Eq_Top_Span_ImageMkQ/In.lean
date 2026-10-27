import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.Submodule.GetDecompose.in.SMulTop.of.In_SMulTop
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
Homogeneous element differs from a homogeneous span combination by an augmentation-ideal multiple
(atlas decompose_mod_P).

[decompose_mod_P](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SyzygiesKoszul.lean)
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
  {T : Finset M}
  {d : ℕ}
  {m : M}
-- given
  (hinter : DirectSum.IsInternal ℳ)
  (hsmul : ∀ (i j : ℕ) (s : S) (m : M), s ∈ 𝒮 j → m ∈ ℳ i → s • m ∈ ℳ (i + j))
  (hThom : ∀ t ∈ T, ∃ d, t ∈ ℳ d)
  (hTspan : Submodule.span k (((Ideal.span (⋃ (i : ℕ) (_ : 0 < i), (𝒮 i : Set S))) • (⊤ : Submodule S M)).mkQ '' ↑T) = ⊤)
  (hm : m ∈ ℳ d) :
-- imply
  ∃ (v : M), v ∈ Submodule.span k (↑T ∩ (ℳ d : Set M)) ∧
    (m - v) ∈ ℳ d ∧ (m - v) ∈ (Ideal.span (⋃ (i : ℕ) (_ : 0 < i), (𝒮 i : Set S))) • (⊤ : Submodule S M) := by
-- proof
  classical
  set P := (Ideal.span (⋃ (i : ℕ) (_ : 0 < i), (𝒮 i : Set S))) • (⊤ : Submodule S M)
  have : DirectSum.Decomposition ℳ := hinter.chooseDecomposition
  have hm_quot : P.mkQ m ∈ Submodule.span k ((P.mkQ.restrictScalars k) '' ↑T) := by
    change P.mkQ m ∈ Submodule.span k (P.mkQ '' ↑T)
    exact hTspan.symm ▸ Submodule.mem_top
  rw [Submodule.span_image, Submodule.mem_map] at hm_quot
  obtain ⟨y, hy, hym⟩ := hm_quot
  rw [Submodule.mem_span_finset] at hy
  obtain ⟨c, _, hc⟩ := hy
  have hsum_in_P : m - ∑ t ∈ T, c t • t ∈ P := by
    have key : P.mkQ (m - ∑ t ∈ T, c t • t) = 0 := by
      simp only [map_sub, map_sum]
      rw [show P.mkQ m = (P.mkQ.restrictScalars k) y from hym.symm, ← hc, map_sum, sub_eq_zero]
      apply Finset.sum_congr rfl
      intro t _; exact ((P.mkQ.restrictScalars k).map_smul (c t) t).symm
    rwa [P.mkQ_apply, Submodule.Quotient.mk_eq_zero] at key
  set v := ∑ t ∈ T.filter (fun t => t ∈ ℳ d), c t • t
  refine ⟨v, ?_, ?_, ?_⟩
  ·
    apply Submodule.sum_mem; intro t ht; rw [Finset.mem_filter] at ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Finset.mem_coe.mpr ht.1, ht.2⟩)
  ·
    apply (ℳ d).sub_mem hm
    apply Submodule.sum_mem; intro t ht; rw [Finset.mem_filter] at ht
    exact (ℳ d).smul_mem _ ht.2
  ·
    set z := m - ∑ t ∈ T, c t • t
    have hmv_d : m - v ∈ ℳ d := by
      apply (ℳ d).sub_mem hm
      apply Submodule.sum_mem
      intro t ht
      rw [Finset.mem_filter] at ht
      exact (ℳ d).smul_mem _ ht.2
    suffices h_decomp : (↑((DirectSum.decompose ℳ z) d) : M) = m - v by
      rw [← h_decomp]
      exact Submodule.GetDecompose.in.SMulTop.of.In_SMulTop (𝒮 := 𝒮) (ℳ := ℳ) hsmul hsum_in_P
    set w := ∑ t ∈ T.filter (fun t => t ∉ ℳ d), c t • t
    have hz_split : z = (m - v) - w := by
      simp only [z, v, w, sub_sub]
      congr 1
      rw [← Finset.sum_union (s₁ := T.filter (· ∈ ℳ d)) (s₂ := T.filter (· ∉ ℳ d))]
      ·
        congr 1
        ext x
        simp [Finset.mem_filter, Finset.mem_union]
        tauto
      · exact Finset.disjoint_filter.mpr (fun x _ h1 h2 => h2 h1)
    conv_lhs => rw [hz_split]
    have hde : DirectSum.decompose ℳ ((m - v) - w) =
        DirectSum.decompose ℳ (m - v) - DirectSum.decompose ℳ w :=
      map_sub (DirectSum.decomposeAddEquiv ℳ) _ _
    rw [hde]
    simp only [DirectSum.sub_apply, AddSubgroupClass.coe_sub,
      DirectSum.decompose_of_mem_same ℳ hmv_d]
    suffices hw0 : (↑((DirectSum.decompose ℳ w) d) : M) = 0 by
      rw [hw0, sub_zero]
    change (↑((DirectSum.decomposeAddEquiv ℳ w) d) : M) = 0
    rw [show w = ∑ t ∈ T.filter (fun t => t ∉ ℳ d), c t • t from rfl,
      map_sum (DirectSum.decomposeAddEquiv ℳ)]
    have key2 : (↑((∑ x ∈ T.filter (fun t => t ∉ ℳ d),
      (DirectSum.decomposeAddEquiv ℳ) (c x • x)) d) : M) =
      ↑(∑ x ∈ T.filter (fun t => t ∉ ℳ d),
        ((DirectSum.decomposeAddEquiv ℳ) (c x • x)) d : ↥(ℳ d)) := by
      congr 1; exact DFinsupp.finsetSum_apply _ _ _
    rw [key2, AddSubmonoidClass.coe_finsetSum]
    apply Finset.sum_eq_zero
    intro t ht; rw [Finset.mem_filter] at ht
    obtain ⟨hT, hnd⟩ := ht
    obtain ⟨e, he⟩ := hThom t hT
    have hne : e ≠ d := fun heq => hnd (heq ▸ he)
    show (↑((DirectSum.decomposeAddEquiv ℳ (c t • t)) d) : M) = 0
    change (↑((DirectSum.decompose ℳ (c t • t)) d) : M) = 0
    exact DirectSum.decompose_of_mem_ne ℳ ((ℳ e).smul_mem _ he) hne


-- created on 2026-10-24
