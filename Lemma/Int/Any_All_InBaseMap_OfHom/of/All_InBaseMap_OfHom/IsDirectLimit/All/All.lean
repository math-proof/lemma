import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_Mathlib_Algebra_IsDirectLimit
open CategoryTheory AlgebraicGeometry


/--
[AlgebraicGeometry_exists_forall_specMap_base_mem_of_isDirectLimit](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_exists_forall_specMap_base_mem_of_isDirectLimit.lean)
-/
@[path]
private lemma main
  {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
  {G : ι → Type u} [∀ i, CommRing (G i)]
  {φ : ∀ i j : ι, i ≤ j → G i →+* G j} [DirectedSystem G fun i j h => ⇑(φ i j h)]
  {R : Type u} [CommRing R]
  {g : ∀ i, G i →+* R}
  {i : ι}
  {W : (Spec (CommRingCat.of (G i))).Opens}
-- given
  (hR : IsDirectLimit (fun i j h => ⇑(φ i j h)) fun i => ⇑(g i))
  (hW : ∀ p : Spec (CommRingCat.of R), (Spec.map (CommRingCat.ofHom (g i))).base p ∈ W) :
-- imply
  ∃ (j : ι) (hij : i ≤ j), ∀ q : Spec (CommRingCat.of (G j)), (Spec.map (CommRingCat.ofHom (φ i j hij))).base q ∈ W := by
-- proof
  classical
  obtain ⟨WS, hWSo, hWS⟩ : ∃ WS : Set (PrimeSpectrum (G i)), IsOpen WS ∧
      WS = (W : Set (Spec (CommRingCat.of (G i)))) := ⟨_, W.2, rfl⟩
  let B := {f : G i // ((PrimeSpectrum.basicOpen f : TopologicalSpace.Opens (PrimeSpectrum (G i))) : Set _) ⊆ WS}
  have hW' : ∀ p : PrimeSpectrum R, PrimeSpectrum.comap (g i) p ∈ WS := fun p => by rw [hWS]; exact hW p
  have hcov : Set.range (PrimeSpectrum.comap (g i)) ⊆ ⋃ f : B, ((PrimeSpectrum.basicOpen f.1 :
    TopologicalSpace.Opens (PrimeSpectrum (G i))) : Set _) := by
    rintro x ⟨p, rfl⟩
    obtain ⟨v, ⟨r, rfl⟩, hxv, hvW⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (hW' p) hWSo
    exact Set.mem_iUnion.2 ⟨⟨r, hvW⟩, hxv⟩
  have hK : IsCompact (Set.range (PrimeSpectrum.comap (g i))) :=
    isCompact_range (PrimeSpectrum.continuous_comap (g i))
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun f : B => ((PrimeSpectrum.basicOpen f.1 :
    TopologicalSpace.Opens (PrimeSpectrum (G i))) : Set _)) (fun f => (PrimeSpectrum.basicOpen f.1).2) hcov
  let v : t → R := fun f => g i f.1.1
  have h1 : (1 : R) ∈ Ideal.span (Set.range v) := by
    by_contra h1
    have hne : Ideal.span (Set.range v) ≠ ⊤ := fun h => h1 (h.symm ▸ Submodule.mem_top)
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    let p : PrimeSpectrum R := ⟨m, hm.isPrime⟩
    have hp : PrimeSpectrum.comap (g i) p ∈ ⋃ f ∈ t, ((PrimeSpectrum.basicOpen f.1 :
      TopologicalSpace.Opens (PrimeSpectrum (G i))) : Set _) := ht ⟨p, rfl⟩
    simp only [Set.mem_iUnion] at hp
    obtain ⟨f, hft, hf⟩ := hp
    rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen] at hf
    apply hf
    show g i f.1 ∈ m
    exact hle (Ideal.subset_span ⟨⟨f, hft⟩, rfl⟩)
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 h1
  choose j b hb using fun f : t => hR.surj (c f)
  obtain ⟨J, hJ⟩ := Finset.exists_le (insert i (Finset.univ.image j))
  have hiJ : i ≤ J := hJ i (Finset.mem_insert_self _ _)
  have hjJ : ∀ f, j f ≤ J := fun f => hJ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
  let s : G J := ∑ f, φ (j f) J (hjJ f) (b f) * φ i J hiJ f.1.1
  have hs : g J s = g J 1 := by
    simp only [s, map_sum, map_mul, map_one]
    rw [← hc]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [hR.compatibility, hR.compatibility, hb]
  obtain ⟨K, hJK, _, hK⟩ := hR.inj J J s 1 hs
  refine ⟨K, hiJ.trans hJK, fun q => ?_⟩
  have hK1 : ∑ f, φ (j f) K ((hjJ f).trans hJK) (b f) * φ i K (hiJ.trans hJK) f.1.1 = 1 := by
    have := hK
    simp only [s, map_sum, map_mul, map_one] at this
    rw [← this]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [DirectedSystem.map_map' (fun i j h => φ i j h), DirectedSystem.map_map' (fun i j h => φ i j h)]
  have hq : ∃ f : t, φ i K (hiJ.trans hJK) f.1.1 ∉ q.asIdeal := by
    by_contra hall
    push Not at hall
    apply q.2.ne_top
    rw [Ideal.eq_top_iff_one, ← hK1]
    exact Ideal.sum_mem _ fun f _ => Ideal.mul_mem_left _ _ (hall f)
  obtain ⟨f, hf⟩ := hq
  have goal : PrimeSpectrum.comap (φ i K (hiJ.trans hJK)) q ∈ WS := by
    apply f.1.2
    rwa [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen]
  rwa [hWS] at goal


-- created on 2026-10-23
