import Mathlib
import sympy.Basic
open scoped InnerProductSpace
open Filter Topology
open InnerProductSpace
open TopologicalSpace

/--
[norm_eq_sqrt_inner](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean)
-/
@[path]
lemma norm_eq_sqrt_inner
  [RCLike 𝕜]
  [SeminormedAddCommGroup H]
  [InnerProductSpace 𝕜 H]
  {x : H} :
-- imply
  ‖x‖ = Real.sqrt (RCLike.re ⟪x, x⟫_𝕜) :=
-- proof
  norm_eq_sqrt_re_inner x

/--
[cauchy_schwarz](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean)
-/
@[path]
lemma cauchy_schwarz
  [RCLike 𝕜]
  [SeminormedAddCommGroup H]
  [InnerProductSpace 𝕜 H]
  {x y : H} :
-- imply
  ‖⟪x, y⟫_𝕜‖ ≤ ‖x‖ * ‖y‖ :=
-- proof
  norm_inner_le_norm x y

/--
[parallelogram_law_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean)
-/
@[path]
lemma parallelogram_law_iff
  {𝕜 : Type*}
  [RCLike 𝕜]
  [NormedAddCommGroup H]
  [NormedSpace 𝕜 H] :
-- imply
  (∀ x y : H, ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2)) ↔ Nonempty (InnerProductSpace 𝕜 H) := by
-- proof
  constructor
  · intro h
    have h' : ∀ x y : H,
      ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖) := by
      intro x y
      have := h x y
      simp only [sq] at this
      exact this
    exact ⟨InnerProductSpace.ofNorm 𝕜 h'⟩
  · intro ⟨ip⟩ x y
    exact @parallelogram_law_with_norm 𝕜 H _ _ ip x y

/--
[bessel_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean)
-/
@[path]
lemma bessel_inequality
  [RCLike 𝕜]
  [SeminormedAddCommGroup H]
  [InnerProductSpace 𝕜 H]
  {v : ι → H}
  {x : H}
-- given
  (hv : Orthonormal 𝕜 v) :
-- imply
  ∑' i, ‖@inner 𝕜 H _ x (v i)‖ ^ 2 ≤ ‖x‖ ^ 2 := by
-- proof
  simp_rw [norm_inner_symm x (v _)]
  exact hv.tsum_inner_products_le x

/--
[inner_tendsto_of_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean)
-/
@[path]
lemma inner_tendsto_of_tendsto
  {𝕜 : Type*}
  [RCLike 𝕜]
  {E : Type*}
  [SeminormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]
  {x : ℕ → E}
  {y : ℕ → E}
  {a b : E}
-- given
  (hx : Tendsto x atTop (nhds a))
  (hy : Tendsto y atTop (nhds b)) :
-- imply
  Tendsto (fun n => @inner 𝕜 E _ (x n) (y n)) atTop (nhds (@inner 𝕜 E _ a b)) :=
-- proof
  hx.inner hy

/--
[parseval_identity_hilbertBasis](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean)
-/
@[path]
lemma parseval_identity_hilbertBasis
  [RCLike 𝕜]
  [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H]
  {b : HilbertBasis ι 𝕜 H}
  {u : H} :
-- imply
  ∑' i, ‖@inner 𝕜 H _ u (b i)‖ ^ 2 = ‖u‖ ^ 2 := by
-- proof
  simp_rw [norm_inner_symm u (b _)]
  simp_rw [← b.repr_apply_apply]
  rw [← b.repr.norm_map u]
  have h := lp.inner_eq_tsum (𝕜 := 𝕜) (G := fun _ : ι => 𝕜) (b.repr u) (b.repr u)
  have hlhs : @inner 𝕜 _ _ (b.repr u) (b.repr u) = (↑(‖b.repr u‖ ^ 2) : 𝕜) := by
    rw [inner_self_eq_norm_sq_to_K]; push_cast; ring
  conv at h => rhs; arg 1; ext i; rw [inner_self_eq_norm_sq_to_K]
  rw [hlhs] at h
  exact_mod_cast h.symm

/--
[parseval_identity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean)
-/
@[path]
lemma parseval_identity
  [RCLike 𝕜]
  [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H]
  [CompleteSpace H]
  {e : ι → H}
  {u : H}
-- given
  (he : Orthonormal 𝕜 e)
  (hcomplete : ⊤ ≤ (Submodule.span 𝕜 (Set.range e)).topologicalClosure) :
-- imply
  ∑' i, ‖@inner 𝕜 H _ u (e i)‖ ^ 2 = ‖u‖ ^ 2 := by
-- proof
  let b : HilbertBasis ι 𝕜 H := HilbertBasis.mk he hcomplete
  have hbe : ∀ i, (b : ι → H) i = e i := fun i => congr_fun (HilbertBasis.coe_mk he hcomplete) i
  simp_rw [← hbe]
  exact parseval_identity_hilbertBasis (b := b) (u := u)

/--
[separable_hilbert_isomorphic_ell2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean)
-/
@[path]
lemma separable_hilbert_isomorphic_ell2
  [RCLike 𝕜]
  [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H]
  {b : HilbertBasis ℕ 𝕜 H} :
-- imply
  Nonempty (H ≃ₗᵢ[𝕜] ↥(lp (fun _ : ℕ => 𝕜) 2)) :=
-- proof
  ⟨b.repr⟩

/--
[orthogonalProjection_is_projection](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean)
-/
@[path]
lemma orthogonalProjection_is_projection
  [RCLike 𝕜]
  [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H]
  {M : Submodule 𝕜 H}
  [M.HasOrthogonalProjection] :
-- imply
  (∀ x : H, M.orthogonalProjectionOnto (M.orthogonalProjectionOnto x : H) = M.orthogonalProjectionOnto x) ∧ ‖M.starProjection‖ ≤ 1 :=
-- proof
  ⟨fun _ => Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _,
    Submodule.starProjection_norm_le M⟩

/--
[riesz_representation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean)
-/
@[path]
lemma riesz_representation
  [RCLike 𝕜]
  [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H]
  [CompleteSpace H]
  {f : H →L[𝕜] 𝕜} :
-- imply
  ∃! y : H, (∀ x : H, f x = ⟪y, x⟫_𝕜) ∧ ‖f‖ = ‖y‖ := by
-- proof
  refine ⟨(toDual 𝕜 H).symm f, ⟨fun x => ?_, ?_⟩, fun y ⟨hy, _⟩ => ?_⟩
  · exact (toDual_symm_apply (𝕜 := 𝕜)).symm
  · rw [← LinearIsometryEquiv.norm_map (toDual 𝕜 H) ((toDual 𝕜 H).symm f),
    LinearIsometryEquiv.apply_symm_apply]
  · have h : (toDual 𝕜 H) y = f := by
      ext x
      rw [toDual_apply_apply, hy x]
    rw [← h, LinearIsometryEquiv.symm_apply_apply]

/--
[separable_of_countable_hilbertBasis](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean)
-/
@[path]
lemma separable_of_countable_hilbertBasis
  [RCLike 𝕜]
  [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H]
  [Countable ι]
  {b : HilbertBasis ι 𝕜 H} :
-- imply
  SeparableSpace H := by
-- proof
  have hcount : (Set.range b).Countable := Set.countable_range b
  have hsep_range : IsSeparable (Set.range (b : ι → H)) := hcount.isSeparable
  have hsep_span : IsSeparable (Submodule.span 𝕜 (Set.range (b : ι → H)) : Set H) :=
    hsep_range.span
  obtain ⟨c, hc_count, hc_sub⟩ := hsep_span
  refine SeparableSpace.mk ⟨c, hc_count, ?_⟩
  rw [dense_iff_closure_eq]
  have h1 : (Submodule.span 𝕜 (Set.range (b : ι → H)) : Set H) ⊆ closure c := hc_sub
  have h2 : closure (Submodule.span 𝕜 (Set.range (b : ι → H)) : Set H) ⊆ closure c :=
    closure_minimal h1 isClosed_closure
  have h3 : closure (Submodule.span 𝕜 (Set.range (b : ι → H)) : Set H) = Set.univ := by
    have h := b.dense_span
    have hcoe := Submodule.topologicalClosure_coe (Submodule.span 𝕜 (Set.range (b : ι → H)))
    rw [h] at hcoe
    simp only [Submodule.top_coe] at hcoe
    exact hcoe.symm
  exact Set.eq_univ_of_univ_subset (h3 ▸ h2)


-- created on 2026-10-23

-- updated on 2026-10-24
