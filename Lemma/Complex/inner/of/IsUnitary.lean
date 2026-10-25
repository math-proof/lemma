import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.LieGroups.code.KFiniteProps
open ContinuousRep hiding orthogonalProjection_intertwines_subrep_val repEquiv_of_bijective_repHom repEquiv_trans repEquiv_symm mem_orthogonal_sSup sSup_orthogonal_sSup total_variation_eval_cont blt_alg_hom_extend
open scoped ComplexOrder
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.overlappingInstances false


/--
[unitary_inner_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma unitary_inner_invariant
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
  [NormedAddCommGroup E]
  [InnerProductSpace ℂ E]
  [CompleteSpace E]
  {π : ContinuousRep G E}
  {g : G}
  {v w : E}
-- given
  (hU : π.IsUnitary) :
-- imply
  @inner ℂ _ _ ((π.toMonoidHom g) v) ((π.toMonoidHom g) w) = @inner ℂ _ _ v w := by
-- proof
  rw [← ContinuousLinearMap.adjoint_inner_left]
  congr 1
  have h := (hU g).1
  have hv : (ContinuousLinearMap.adjoint (π.toMonoidHom g) * π.toMonoidHom g) v = v := by
    rw [h]
    rfl
  exact hv

/--
[unitary_orthogonal_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma unitary_orthogonal_invariant
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  [NormedAddCommGroup E]
  [InnerProductSpace ℂ E]
  [CompleteSpace E]
  {π : ContinuousRep G E}
  {W : Submodule ℂ E}
  {g : G}
  {v : E}
-- given
  (hU : π.IsUnitary)
  (hW : ∀ (g : G) (v : E), v ∈ W → (π.toMonoidHom g) v ∈ W)
  (hv : v ∈ Wᗮ) :
-- imply
  (π.toMonoidHom g) v ∈ Wᗮ := by
-- proof
  rw [Submodule.mem_orthogonal'] at hv ⊢
  intro w hw
  rw [← ContinuousLinearMap.adjoint_inner_right, unitary_adjoint_eq_inv π hU g]
  exact hv _ (hW g⁻¹ w hw)

/--
[orthogonalProjection_intertwines_subrep_val](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma orthogonalProjection_intertwines_subrep_val
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
  [NormedAddCommGroup E]
  [InnerProductSpace ℂ E]
  [CompleteSpace E]
  [IsTopologicalGroup G]
  {π : ContinuousRep G E}
  {K : Subgroup G}
  {W₁ W₂ : Submodule ℂ E}
  [W₂.HasOrthogonalProjection]
  {v : ↥W₁}
-- given
  (hU : π.IsUnitary)
  (hW₁ : (π.restrictSubgroup K).IsInvariantSubspace W₁)
  (hW₂ : (π.restrictSubgroup K).IsInvariantSubspace W₂) :
-- imply
  (orthogonalProjection_intertwines_subrep π hU K W₁ W₂ hW₁ hW₂).toContinuousLinearMap v = W₂.orthogonalProjectionOnto (v : E) := by
-- proof
  exact ContinuousRep.orthogonalProjection_intertwines_subrep_val π hU K W₁ W₂ hW₁ hW₂ v


/--
[continuous_inverse_of_bijective_clm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma continuous_inverse_of_bijective_clm
  [NormedAddCommGroup V₁]
  [NormedSpace ℂ V₁]
  [CompleteSpace V₁]
  [NormedAddCommGroup V₂]
  [NormedSpace ℂ V₂]
  [CompleteSpace V₂]
  {f : V₁ →L[ℂ] V₂}
-- given
  (hbij : Function.Bijective f) :
-- imply
  Continuous (LinearEquiv.ofBijective f.toLinearMap hbij).symm :=
-- proof
  (LinearEquiv.ofBijective f.toLinearMap hbij).continuous_symm f.continuous

/--
[repEquiv_of_bijective_repHom](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma repEquiv_of_bijective_repHom
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
  [NormedAddCommGroup V₁]
  [NormedSpace ℂ V₁]
  [TopologicalSpace V₁]
  [CompleteSpace V₁]
  [NormedAddCommGroup V₂]
  [NormedSpace ℂ V₂]
  [TopologicalSpace V₂]
  [CompleteSpace V₂]
  {π₁ : ContinuousRep G V₁}
  {π₂ : ContinuousRep G V₂}
  {T : RepHom π₁ π₂}
-- given
  (hbij : Function.Bijective T.toContinuousLinearMap) :
-- imply
  Nonempty (RepEquiv π₁ π₂) := by
-- proof
  exact ContinuousRep.repEquiv_of_bijective_repHom π₁ π₂ T hbij


/--
[repEquiv_trans](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma repEquiv_trans
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
  [AddCommGroup V₁]
  [Module ℂ V₁]
  [TopologicalSpace V₁]
  [AddCommGroup V₂]
  [Module ℂ V₂]
  [TopologicalSpace V₂]
  [AddCommGroup V₃]
  [Module ℂ V₃]
  [TopologicalSpace V₃]
  {π₁ : ContinuousRep G V₁}
  {π₂ : ContinuousRep G V₂}
  {π₃ : ContinuousRep G V₃}
-- given
  (h₁ : Nonempty (RepEquiv π₁ π₂))
  (h₂ : Nonempty (RepEquiv π₂ π₃)) :
-- imply
  Nonempty (RepEquiv π₁ π₃) := by
-- proof
  exact ContinuousRep.repEquiv_trans h₁ h₂


/--
[repEquiv_symm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma repEquiv_symm
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
  [AddCommGroup V₁]
  [Module ℂ V₁]
  [TopologicalSpace V₁]
  [AddCommGroup V₂]
  [Module ℂ V₂]
  [TopologicalSpace V₂]
  {π₁ : ContinuousRep G V₁}
  {π₂ : ContinuousRep G V₂}
-- given
  (h : Nonempty (RepEquiv π₁ π₂)) :
-- imply
  Nonempty (RepEquiv π₂ π₁) := by
-- proof
  exact ContinuousRep.repEquiv_symm h


/--
[irreducible_subspaces_orthogonal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma irreducible_subspaces_orthogonal
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
  [NormedAddCommGroup E]
  [InnerProductSpace ℂ E]
  [CompleteSpace E]
  [IsTopologicalGroup G]
  [AddCommGroup Wσ]
  [Module ℂ Wσ]
  [TopologicalSpace Wσ]
  [AddCommGroup Wτ]
  [Module ℂ Wτ]
  [TopologicalSpace Wτ]
  {π : ContinuousRep G E}
  {K : Subgroup G}
  {σ : ContinuousRep K Wσ}
  {τ : ContinuousRep K Wτ}
  {W₁ W₂ : Submodule ℂ E}
-- given
  (hU : π.IsUnitary)
  (hW₁ : (π.restrictSubgroup K).IsInvariantSubspace W₁)
  (hW₂ : (π.restrictSubgroup K).IsInvariantSubspace W₂)
  (hirr₁ : ((π.restrictSubgroup K).subrepresentation W₁ hW₁).IsIrreducible)
  (hirr₂ : ((π.restrictSubgroup K).subrepresentation W₂ hW₂).IsIrreducible)
  (hiso₁ : Nonempty (RepEquiv ((π.restrictSubgroup K).subrepresentation W₁ hW₁) σ))
  (hiso₂ : Nonempty (RepEquiv ((π.restrictSubgroup K).subrepresentation W₂ hW₂) τ))
  (hne : ¬ Nonempty (RepEquiv σ τ)) :
-- imply
  W₁.IsOrtho W₂ := by
-- proof
  haveI : CompleteSpace ↥W₁ := hW₁.isClosed.completeSpace_coe
  haveI : CompleteSpace ↥W₂ := hW₂.isClosed.completeSpace_coe
  haveI : W₂.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace W₂
  set T := orthogonalProjection_intertwines_subrep π hU K W₁ W₂ hW₁ hW₂
  rcases schur_zero_or_iso_continuous
    ((π.restrictSubgroup K).subrepresentation W₁ hW₁)
    ((π.restrictSubgroup K).subrepresentation W₂ hW₂)
    hirr₁ hirr₂ T with hzero | hbij
  ·
    intro v hv
    have hTval := orthogonalProjection_intertwines_subrep_val (v := ⟨v, hv⟩) hU hW₁ hW₂
    have hTzero : T.toContinuousLinearMap ⟨v, hv⟩ = 0 := hzero ⟨v, hv⟩
    have hproj0 : W₂.orthogonalProjectionOnto (v : E) = 0 := by
      rw [← hTval]
      exact hTzero
    exact (Submodule.orthogonalProjectionOnto_eq_zero_iff).mp hproj0
  ·
    exfalso
    apply hne
    have h12 := repEquiv_of_bijective_repHom
      (π₁ := (π.restrictSubgroup K).subrepresentation W₁ hW₁)
      (π₂ := (π.restrictSubgroup K).subrepresentation W₂ hW₂)
      (T := T) hbij
    exact repEquiv_trans (repEquiv_trans (repEquiv_symm hiso₁) h12) hiso₂

/--
[mem_orthogonal_sSup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma mem_orthogonal_sSup
  [NormedAddCommGroup F]
  [InnerProductSpace ℂ F]
  {T : Set (Submodule ℂ F)}
  {v : F}
-- given
  (h : ∀ W ∈ T, v ∈ Wᗮ) :
-- imply
  v ∈ (sSup T)ᗮ := by
-- proof
  exact ContinuousRep.mem_orthogonal_sSup h


/--
[sSup_orthogonal_sSup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma sSup_orthogonal_sSup
  [NormedAddCommGroup F]
  [InnerProductSpace ℂ F]
  {S T : Set (Submodule ℂ F)}
-- given
  (h : ∀ U ∈ S, ∀ W ∈ T, U.IsOrtho W) :
-- imply
  (sSup S).IsOrtho (sSup T) := by
-- proof
  exact ContinuousRep.sSup_orthogonal_sSup h


/--
[isotypicComponent_orthogonal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma isotypicComponent_orthogonal
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
  [NormedAddCommGroup E]
  [InnerProductSpace ℂ E]
  [CompleteSpace E]
  [IsTopologicalGroup G]
  [AddCommGroup Wσ]
  [Module ℂ Wσ]
  [TopologicalSpace Wσ]
  [AddCommGroup Wτ]
  [Module ℂ Wτ]
  [TopologicalSpace Wτ]
  {π : ContinuousRep G E}
  {K : Subgroup G}
  {σ : ContinuousRep K Wσ}
  {τ : ContinuousRep K Wτ}
-- given
  (hU : π.IsUnitary)
  (hne : ¬ Nonempty (RepEquiv σ τ)) :
-- imply
  (IsotypicComponent π K σ).IsOrtho (IsotypicComponent π K τ) := by
-- proof
  unfold IsotypicComponent
  apply sSup_orthogonal_sSup
  intro W₁ hW₁ W₂ hW₂
  obtain ⟨hW₁inv, hirr₁, hiso₁⟩ := hW₁
  obtain ⟨hW₂inv, hirr₂, hiso₂⟩ := hW₂
  exact irreducible_subspaces_orthogonal (π := π) (K := K) (σ := σ) (τ := τ)
    (W₁ := W₁) (W₂ := W₂) hU hW₁inv hW₂inv hirr₁ hirr₂ hiso₁ hiso₂ hne

/--
[discreteMeasureRep_extends](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma discreteMeasureRep_extends
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  {V : Type uG}
  [NormedAddCommGroup V]
  [NormedSpace ℂ V]
  (π : G →* (V →L[ℂ] V))
  {g : G} :
-- imply
  discreteMeasureRep π (MonoidAlgebra.single g 1) = π g := by
-- proof
  simp [discreteMeasureRep, MonoidAlgebra.lift_single]

/--
[discreteMeasureRep_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma discreteMeasureRep_unique
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  {V : Type uG}
  [NormedAddCommGroup V]
  [NormedSpace ℂ V]
  (π : G →* (V →L[ℂ] V))
  {φ : MonoidAlgebra ℂ G →ₐ[ℂ] (V →L[ℂ] V)}
-- given
  (hφ : ∀ g : G, φ (MonoidAlgebra.single g 1) = π g) :
-- imply
  φ = discreteMeasureRep π := by
-- proof
  have key : (MonoidAlgebra.lift ℂ (V →L[ℂ] V) G).symm φ = π := by
    ext g : 1
    rw [MonoidAlgebra.lift_symm_apply]
    exact hφ g
  have hlift : (MonoidAlgebra.lift ℂ (V →L[ℂ] V) G) π = φ := by
    rw [← key, (MonoidAlgebra.lift ℂ (V →L[ℂ] V) G).apply_symm_apply]
  rw [discreteMeasureRep, ← hlift]

/--
[total_variation_eval_cont](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma total_variation_eval_cont
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  {M : Type uM}
  [Ring M]
  [Algebra ℂ M]
  [TopologicalSpace M]
  [inst : CompactlySupportedMeasureAlgebra G M]
  (f : G → ℝ)
  (hf : Continuous f)
  (hf_nn : ∀ g, 0 ≤ f g) :
  @Continuous (MonoidAlgebra ℂ G) ℝ (TopologicalSpace.induced (MonoidAlgebra.lift ℂ M G inst.dirac) ‹TopologicalSpace M›) inferInstance (fun μ => μ.sum (fun g c => ‖c‖ * f g)) :=
  ContinuousRep.total_variation_eval_cont f hf hf_nn


/--
[rep_lift_opNorm_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma rep_lift_opNorm_le
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  {V : Type uG}
  [NormedAddCommGroup V]
  [NormedSpace ℂ V]
  (π : G →* (V →L[ℂ] V))
  (μ : MonoidAlgebra ℂ G) :
-- imply
  ‖(MonoidAlgebra.lift ℂ (V →L[ℂ] V) G π) μ‖ ≤ MonoidAlgebra.sum μ (fun g c => ‖c‖ * ‖π g‖) := by
-- proof
  rw [MonoidAlgebra.lift_apply]
  calc ‖μ.coeff.sum (fun g c => c • π g)‖
    ≤ μ.coeff.support.sum (fun g => ‖μ.coeff g • π g‖) := norm_sum_le _ _
    _ = μ.coeff.support.sum (fun g => ‖μ.coeff g‖ * ‖π g‖) := by
      congr 1; ext g; exact norm_smul (μ.coeff g) (π g)
    _ = MonoidAlgebra.sum μ (fun g c => ‖c‖ * ‖π g‖) := by
      simp only [MonoidAlgebra.sum]
      rfl
set_option checkBinderAnnotations false in

/--
[total_variation_eval_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma total_variation_eval_continuous
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  {M : Type uM}
  [Ring M]
  [Algebra ℂ M]
  [TopologicalSpace M]
  [CompactlySupportedMeasureAlgebra G M]
  (f : G → ℝ)
  (hf : Continuous f)
  (hf_nn : ∀ g, 0 ≤ f g) :
  @Continuous (MonoidAlgebra ℂ G) ℝ (TopologicalSpace.induced (MonoidAlgebra.lift ℂ M G CompactlySupportedMeasureAlgebra.dirac) ‹TopologicalSpace M›) inferInstance (fun μ => μ.sum (fun g c => ‖c‖ * f g)) :=
  total_variation_eval_cont f hf hf_nn

/--
[rep_continuous_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma rep_continuous_theorem
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  {M : Type uM}
  [Ring M]
  [Algebra ℂ M]
  [TopologicalSpace M]
  [ContinuousAdd M]
  [ContinuousMul M]
  [CompactlySupportedMeasureAlgebra G M]
  {V : Type uG}
  [NormedAddCommGroup V]
  [NormedSpace ℂ V]
  (π : G →* (V →L[ℂ] V))
-- given
  (hcont_norm : Continuous (fun g : G => ‖(π g : V →L[ℂ] V)‖)) :
-- imply
  @Continuous (MonoidAlgebra ℂ G) (V →L[ℂ] V) (TopologicalSpace.induced (MonoidAlgebra.lift ℂ M G CompactlySupportedMeasureAlgebra.dirac) ‹TopologicalSpace M›) (by infer_instance) (MonoidAlgebra.lift ℂ (V →L[ℂ] V) G π) := by
-- proof
  let δ_lift := MonoidAlgebra.lift ℂ M G CompactlySupportedMeasureAlgebra.dirac
  letI t_ind : TopologicalSpace (MonoidAlgebra ℂ G) :=
    TopologicalSpace.induced δ_lift ‹TopologicalSpace M›
  haveI instCNM : ContinuousNeg M := by
    constructor
    have : (Neg.neg : M → M) = (fun a => (-1 : M) * a) := by
      ext a; exact (neg_one_mul a).symm
    rw [this]; exact continuous_const.mul continuous_id
  haveI : IsTopologicalAddGroup M :=
    { toContinuousAdd := ‹ContinuousAdd M›, toContinuousNeg := instCNM }
  haveI : IsTopologicalAddGroup (MonoidAlgebra ℂ G) :=
    isTopologicalAddGroup_induced δ_lift
  let π_lift := MonoidAlgebra.lift ℂ (V →L[ℂ] V) G π
  change @Continuous _ _ t_ind _ π_lift
  have h_tendsto : Filter.Tendsto π_lift (@nhds _ t_ind 0) (nhds 0) := by
    apply squeeze_zero_norm (fun μ => rep_lift_opNorm_le π μ)
    have h0 : MonoidAlgebra.sum (0 : MonoidAlgebra ℂ G) (fun g c => ‖c‖ * ‖(π g : V →L[ℂ] V)‖) = 0 := by
      simp [MonoidAlgebra.sum, Finsupp.sum_zero_index]
    rw [← h0]
    exact (total_variation_eval_cont
      (fun g => ‖(π g : V →L[ℂ] V)‖) hcont_norm (fun g => norm_nonneg _)).continuousAt.tendsto
  have h_cont_hom : Continuous (π_lift.toAddMonoidHom : MonoidAlgebra ℂ G →+ (V →L[ℂ] V)) :=
    continuous_of_tendsto_nhds_zero π_lift.toAddMonoidHom h_tendsto
  convert h_cont_hom using 1

/--
[discrete_measures_sequentially_dense](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma discrete_measures_sequentially_dense
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  {M : Type uM}
  [Ring M]
  [Algebra ℂ M]
  [TopologicalSpace M]
  [inst : CompactlySupportedMeasureAlgebra G M]
  [FrechetUrysohnSpace M] :
-- imply
  ∀ (m : M), m ∈ seqClosure (Set.range (MonoidAlgebra.lift ℂ M G inst.dirac)) := by
-- proof
  intro m
  have hm_clos := inst.discrete_in_closure m
  rw [mem_closure_iff_seq_limit] at hm_clos
  obtain ⟨x, hx_mem, hx_tendsto⟩ := hm_clos
  exact ⟨x, hx_mem, hx_tendsto⟩

/--
[CompactlySupportedMeasureAlgebra.discrete_dense](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma CompactlySupportedMeasureAlgebra.discrete_dense
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  {M : Type uM}
  [Ring M]
  [Algebra ℂ M]
  [TopologicalSpace M]
  [inst : CompactlySupportedMeasureAlgebra G M] :
-- imply
  Dense (Set.range (MonoidAlgebra.lift ℂ M G inst.dirac)) := by
-- proof
  exact ContinuousRep.CompactlySupportedMeasureAlgebra.discrete_dense


/--
[blt_alg_hom_extend](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma blt_alg_hom_extend
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  {V : Type uG}
  [NormedAddCommGroup V]
  [NormedSpace ℂ V]
  [Semiring α]
  [Semiring β]
  [Semiring γ]
  [Algebra ℂ α]
  [Algebra ℂ β]
  [Algebra ℂ γ]
  [TopologicalSpace β]
  [ContinuousAdd β]
  [ContinuousMul β]
  [TopologicalSpace γ]
  [T2Space γ]
  [ContinuousAdd γ]
  [ContinuousMul γ]
  {ι : α →ₐ[ℂ] β}
  {f : α →ₐ[ℂ] γ}
  {g_fun : β → γ}
-- given
  (h_dense : Dense (Set.range ι))
  (hg_cont : Continuous g_fun)
  (hg_ext : ∀ x : α, g_fun (ι x) = f x) :
-- imply
  ∃ (g : β →ₐ[ℂ] γ), Continuous g ∧ ∀ x : α, g (ι x) = f x := by
-- proof
  exact ContinuousRep.blt_alg_hom_extend h_dense hg_cont hg_ext


/--
[CompactlySupportedMeasureAlgebra.alg_hom_extend](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma CompactlySupportedMeasureAlgebra.alg_hom_extend
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  {M : Type uM}
  [Ring M]
  [Algebra ℂ M]
  [TopologicalSpace M]
  [ContinuousAdd M]
  [ContinuousMul M]
  [inst : CompactlySupportedMeasureAlgebra G M]
  [Ring A]
  [Algebra ℂ A]
  [inst_unif_A : UniformSpace A]
  [CompleteSpace A]
  [T2Space A]
  [ContinuousAdd A]
  [ContinuousMul A]
  [IsUniformAddGroup A]
  {f : MonoidAlgebra ℂ G →ₐ[ℂ] A}
-- given
  (h_dense : Dense (Set.range (MonoidAlgebra.lift ℂ M G inst.dirac)))
  (h_cont : @Continuous (MonoidAlgebra ℂ G) A (TopologicalSpace.induced (MonoidAlgebra.lift ℂ M G inst.dirac) ‹TopologicalSpace M›) inst_unif_A.toTopologicalSpace f) :
-- imply
  ∃ (g : M →ₐ[ℂ] A), Continuous g ∧ ∀ μ : MonoidAlgebra ℂ G, g ((MonoidAlgebra.lift ℂ M G inst.dirac) μ) = f μ := by
-- proof
  exact ContinuousRep.CompactlySupportedMeasureAlgebra.alg_hom_extend h_dense h_cont


/--
[continuous_opNorm_of_jointly_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma continuous_opNorm_of_jointly_continuous
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
  {V : Type uG}
  [NormedAddCommGroup V]
  [NormedSpace ℂ V]
  [FiniteDimensional ℂ V]
  (π : G →* (V →L[ℂ] V))
-- given
  (hcont : Continuous (fun p : G × V => (π p.1) p.2)) :
-- imply
  Continuous (fun g : G => ‖(π g : V →L[ℂ] V)‖) := by
-- proof
  have hπ_cont : Continuous (fun g => (π g : V →L[ℂ] V)) := by
    rw [continuous_clm_apply]
    intro v
    exact hcont.comp (continuous_id.prodMk continuous_const)
  exact continuous_norm.comp hπ_cont

/--
[discreteMeasureRep_continuous_to_opnorm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma discreteMeasureRep_continuous_to_opnorm
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  {V : Type uG}
  [NormedAddCommGroup V]
  [NormedSpace ℂ V]
  [Ring M]
  [Algebra ℂ M]
  [TopologicalSpace M]
  [ContinuousAdd M]
  [ContinuousMul M]
  [CompactlySupportedMeasureAlgebra G M]
  [FrechetUrysohnSpace M]
  (π : G →* (V →L[ℂ] V))
  [FiniteDimensional ℂ V]
-- given
  (hcont : Continuous (fun p : G × V => (π p.1) p.2)) :
-- imply
  @Continuous (MonoidAlgebra ℂ G) (V →L[ℂ] V) (weakTopologyOnDiscreteMeasures (M := M)) (by infer_instance) (discreteMeasureRep π) :=
-- proof
  rep_continuous_theorem (M := M) π (continuous_opNorm_of_jointly_continuous π hcont)

/--
[discreteMeasureRep_weakly_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma discreteMeasureRep_weakly_continuous
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  {V : Type uG}
  [NormedAddCommGroup V]
  [NormedSpace ℂ V]
  [Ring M]
  [Algebra ℂ M]
  [TopologicalSpace M]
  [ContinuousAdd M]
  [ContinuousMul M]
  [CompactlySupportedMeasureAlgebra G M]
  [FrechetUrysohnSpace M]
  (π : G →* (V →L[ℂ] V))
  [FiniteDimensional ℂ V]
-- given
  (hcont : Continuous (fun p : G × V => (π p.1) p.2)) :
-- imply
  @Continuous (MonoidAlgebra ℂ G) (V →L[ℂ] V)
    (weakTopologyOnDiscreteMeasures (M := M)) inferInstance (discreteMeasureRep π) :=
-- proof
  discreteMeasureRep_continuous_to_opnorm (M := M) π hcont

/--
[discreteMeasureRep_BLT_extension](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma discreteMeasureRep_BLT_extension
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  {V : Type uG}
  [NormedAddCommGroup V]
  [NormedSpace ℂ V]
  [Ring M]
  [Algebra ℂ M]
  [TopologicalSpace M]
  [ContinuousAdd M]
  [ContinuousMul M]
  [CompactlySupportedMeasureAlgebra G M]
  [FrechetUrysohnSpace M]
  (π : G →* (V →L[ℂ] V))
  [FiniteDimensional ℂ V]
-- given
  (hcont : Continuous (fun p : G × V => (π p.1) p.2))
  (h_dense : Dense (Set.range (MonoidAlgebra.lift ℂ M G CompactlySupportedMeasureAlgebra.dirac))) :
-- imply
  ∃ (π_ext : M →ₐ[ℂ] (V →L[ℂ] V)), Continuous π_ext ∧ ∀ μ : MonoidAlgebra ℂ G, π_ext ((MonoidAlgebra.lift ℂ M G CompactlySupportedMeasureAlgebra.dirac) μ) = discreteMeasureRep π μ := by
-- proof
  have h_weak_cont : @Continuous (MonoidAlgebra ℂ G) (V →L[ℂ] V)
    (weakTopologyOnDiscreteMeasures (M := M)) _ (discreteMeasureRep π) :=
    discreteMeasureRep_continuous_to_opnorm (M := M) π hcont
  exact CompactlySupportedMeasureAlgebra.alg_hom_extend
    (f := discreteMeasureRep π) h_dense h_weak_cont

/--
[measureRep_exists_extension](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma measureRep_exists_extension
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  {V : Type uG}
  [NormedAddCommGroup V]
  [NormedSpace ℂ V]
  [Ring M]
  [Algebra ℂ M]
  [TopologicalSpace M]
  [ContinuousAdd M]
  [ContinuousMul M]
  [CompactlySupportedMeasureAlgebra G M]
  [FrechetUrysohnSpace M]
  (π : G →* (V →L[ℂ] V))
  [FiniteDimensional ℂ V]
-- given
  (hcont : Continuous (fun p : G × V => (π p.1) p.2)) :
-- imply
  ∃ (π_ext : M →ₐ[ℂ] (V →L[ℂ] V)), Continuous π_ext ∧ (∀ g : G, π_ext (CompactlySupportedMeasureAlgebra.dirac g) = π g) ∧ (∀ μ : MonoidAlgebra ℂ G, π_ext ((MonoidAlgebra.lift ℂ M G CompactlySupportedMeasureAlgebra.dirac) μ) = discreteMeasureRep π μ) := by
-- proof
  obtain ⟨π_ext, h_cont_ext, h_extends⟩ := discreteMeasureRep_BLT_extension (M := M) π hcont
    (CompactlySupportedMeasureAlgebra.discrete_dense (G := G) (M := M))
  exact ⟨π_ext, h_cont_ext, fun g => by
    have := h_extends (MonoidAlgebra.single g 1)
    simp only [discreteMeasureRep, MonoidAlgebra.lift_single, one_smul] at this
    exact this, h_extends⟩

/--
[measureRep_continuous_bilinear](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma measureRep_continuous_bilinear
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  {V : Type uG}
  [NormedAddCommGroup V]
  [NormedSpace ℂ V]
  [Ring M]
  [Algebra ℂ M]
  [TopologicalSpace M]
  [ContinuousAdd M]
  [ContinuousMul M]
  [CompactlySupportedMeasureAlgebra G M]
  [FrechetUrysohnSpace M]
  (π : G →* (V →L[ℂ] V))
  [FiniteDimensional ℂ V]
  {π_ext : M →ₐ[ℂ] (V →L[ℂ] V)}
-- given
  (_hcont : Continuous (fun p : G × V => (π p.1) p.2))
  (_h_extends : ∀ g : G, π_ext (CompactlySupportedMeasureAlgebra.dirac g) = π g)
  (hcont_ext : Continuous π_ext) :
-- imply
  Continuous (fun p : M × V => (π_ext p.1) p.2) :=
-- proof
by
  exact Continuous.comp (isBoundedBilinearMap_apply (𝕜 := ℂ)).continuous
    (Continuous.prodMap hcont_ext continuous_id)

/--
[measureRep_continuous_extension](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma measureRep_continuous_extension
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  {V : Type uG}
  [NormedAddCommGroup V]
  [NormedSpace ℂ V]
  [Ring M]
  [Algebra ℂ M]
  [TopologicalSpace M]
  [ContinuousAdd M]
  [ContinuousMul M]
  [CompactlySupportedMeasureAlgebra G M]
  [FrechetUrysohnSpace M]
  (π : G →* (V →L[ℂ] V))
  [FiniteDimensional ℂ V]
-- given
  (hcont : Continuous (fun p : G × V => (π p.1) p.2)) :
-- imply
  ∃ (π_ext : M →ₐ[ℂ] (V →L[ℂ] V)), (∀ g : G, π_ext (CompactlySupportedMeasureAlgebra.dirac g) = π g) ∧ Continuous π_ext ∧ Continuous (fun p : M × V => (π_ext p.1) p.2) := by
-- proof
  obtain ⟨π_ext, hcont_ext, h_dirac, _h_extends⟩ := measureRep_exists_extension (M := M) π hcont
  exact ⟨π_ext, h_dirac, hcont_ext,
    measureRep_continuous_bilinear (M := M) (π_ext := π_ext) π hcont h_dirac hcont_ext⟩

/--
[measureRep_unique_extension](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma measureRep_unique_extension
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  {V : Type uG}
  [NormedAddCommGroup V]
  [NormedSpace ℂ V]
  [Ring M]
  [Algebra ℂ M]
  [TopologicalSpace M]
  [ContinuousAdd M]
  [ContinuousMul M]
  [CompactlySupportedMeasureAlgebra G M]
  [FrechetUrysohnSpace M]
  (π : G →* (V →L[ℂ] V))
  [CompleteSpace V]
  {φ₁ φ₂ : M →ₐ[ℂ] (V →L[ℂ] V)}
-- given
  (_hcont : Continuous (fun p : G × V => (π p.1) p.2))
  (h₁ : ∀ g : G, φ₁ (CompactlySupportedMeasureAlgebra.dirac g) = π g)
  (h₂ : ∀ g : G, φ₂ (CompactlySupportedMeasureAlgebra.dirac g) = π g)
  (hcont₁ : Continuous (fun p : M × V => (φ₁ p.1) p.2))
  (hcont₂ : Continuous (fun p : M × V => (φ₂ p.1) p.2)) :
-- imply
  φ₁ = φ₂ := by
-- proof
  ext m v
  have hcv₁ : Continuous (fun m : M => (φ₁ m) v) :=
    hcont₁.comp (Continuous.prodMk continuous_id continuous_const)
  have hcv₂ : Continuous (fun m : M => (φ₂ m) v) :=
    hcont₂.comp (Continuous.prodMk continuous_id continuous_const)
  have heq_on : Set.EqOn (fun m => (φ₁ m) v) (fun m => (φ₂ m) v)
    (Set.range (MonoidAlgebra.lift ℂ M G CompactlySupportedMeasureAlgebra.dirac)) := by
    intro m ⟨μ, hμ⟩
    subst hμ
    simp only
    have eq₁ : φ₁.comp (MonoidAlgebra.lift ℂ M G CompactlySupportedMeasureAlgebra.dirac) =
      MonoidAlgebra.lift ℂ (V →L[ℂ] V) G π := by
      ext g; simp [MonoidAlgebra.lift_single, h₁]
    have eq₂ : φ₂.comp (MonoidAlgebra.lift ℂ M G CompactlySupportedMeasureAlgebra.dirac) =
      MonoidAlgebra.lift ℂ (V →L[ℂ] V) G π := by
      ext g; simp [MonoidAlgebra.lift_single, h₂]
    have h1' := congr_fun (congr_arg DFunLike.coe eq₁) μ
    have h2' := congr_fun (congr_arg DFunLike.coe eq₂) μ
    simp [AlgHom.comp_apply] at h1' h2'
    rw [h1', h2']
  have := Continuous.ext_on (CompactlySupportedMeasureAlgebra.discrete_dense (G := G) (M := M)) hcv₁ hcv₂ heq_on
  exact congr_fun this m

/--
[finite_of_allKFiniteFunc](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma finite_of_allKFiniteFunc
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
  [AddCommGroup V]
  [Module ℂ V]
  [TopologicalSpace V]
  [IsTopologicalGroup G]
  [CompactSpace G]
  {K : Subgroup G}
  [CompactSpace K]
-- given
  (hall : ∀ f : ↥K → ℂ, IsKFiniteFunc K f) :
-- imply
  Finite ↥K := by
-- proof
  classical
  have h_fd := hall (Pi.single 1 (1 : ℂ))
  rw [IsKFiniteFunc] at h_fd
  have h_orbit : (Set.range (fun (g : ↥K) (k : ↥K) =>
    (Pi.single (1 : ↥K) (1 : ℂ) : ↥K → ℂ) (g⁻¹ * k))) =
    Set.range (fun (g : ↥K) => (Pi.single g (1 : ℂ) : ↥K → ℂ)) := by
    ext f; simp only [Set.mem_range]
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g, by ext k; simp [Pi.single_apply, inv_mul_eq_one, eq_comm]⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g, by ext k; simp [Pi.single_apply, inv_mul_eq_one, eq_comm]⟩
  rw [h_orbit] at h_fd
  exact (linearIndependent_span (Pi.linearIndependent_single_one (↥K) ℂ)).finite

/--
[isotypicProjection_idempotent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma isotypicProjection_idempotent
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
  [NormedAddCommGroup E]
  [InnerProductSpace ℂ E]
  [CompleteSpace E]
  [IsTopologicalGroup G]
  [CompactSpace G]
  [AddCommGroup Wσ]
  [Module ℂ Wσ]
  [TopologicalSpace Wσ]
  {π : ContinuousRep G E}
  {K : Subgroup G}
  [CompactSpace K]
  {σ : ContinuousRep K Wσ}
-- given
  (_hU : π.IsUnitary) :
-- imply
  (isotypicProjection π K σ).comp (isotypicProjection π K σ) = isotypicProjection π K σ := by
-- proof
  ext v
  simp only [ContinuousLinearMap.comp_apply, isotypicProjection,
    Submodule.subtypeL_apply]
  have h : (IsotypicComponent π K σ).orthogonalProjectionOnto
    (↑((IsotypicComponent π K σ).orthogonalProjectionOnto v)) =
    (IsotypicComponent π K σ).orthogonalProjectionOnto v :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
  rw [h]

/--
[isotypicProjection_range](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma isotypicProjection_range
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
  [NormedAddCommGroup E]
  [InnerProductSpace ℂ E]
  [CompleteSpace E]
  [IsTopologicalGroup G]
  [CompactSpace G]
  [AddCommGroup Wσ]
  [Module ℂ Wσ]
  [TopologicalSpace Wσ]
  {π : ContinuousRep G E}
  {K : Subgroup G}
  [CompactSpace K]
  {σ : ContinuousRep K Wσ}
-- given
  (_hU : π.IsUnitary) :
-- imply
  LinearMap.range (isotypicProjection π K σ).toLinearMap = IsotypicComponent π K σ := by
-- proof
  ext v
  constructor
  · rintro ⟨w, hw⟩
    change (isotypicProjection π K σ) w = v at hw
    rw [isotypicProjection] at hw
    simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply] at hw
    rw [← hw]
    exact ((IsotypicComponent π K σ).orthogonalProjectionOnto w).2
  · intro hv
    refine ⟨v, ?_⟩
    change (isotypicProjection π K σ) v = v
    rw [isotypicProjection]
    simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
    have : (IsotypicComponent π K σ).orthogonalProjectionOnto v = ⟨v, hv⟩ :=
      Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨v, hv⟩
    rw [this]

/--
[kFiniteSubspace_stable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma kFiniteSubspace_stable_eq
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  [AddCommGroup V]
  [Module ℂ V]
  [TopologicalSpace V]
  {π : ContinuousRep G V}
  {K : Subgroup G}
  {g : K}
  {v : V}
-- given
  (hv : v ∈ kFiniteSubspace π K) :
-- imply
  (π.toMonoidHom g) v ∈ kFiniteSubspace π K := by
-- proof
  apply ContinuousRep.kFiniteSubspace_stable π K g v hv

/--
[unitary_adjoint_eq_inv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma unitary_adjoint_eq_inv_eq
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  [NormedAddCommGroup E]
  [InnerProductSpace ℂ E]
  [CompleteSpace E]
  {π : ContinuousRep G E}
  {g : G}
-- given
  (hU : π.IsUnitary) :
-- imply
  ContinuousLinearMap.adjoint (π.toMonoidHom g) = π.toMonoidHom g⁻¹ := by
-- proof
  apply ContinuousRep.unitary_adjoint_eq_inv π hU g

/--
[isotypicComponent_hasOrthogonalProjection](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma isotypicComponent_hasOrthogonalProjection_eq
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
  [NormedAddCommGroup E]
  [InnerProductSpace ℂ E]
  [CompleteSpace E]
  [IsTopologicalGroup G]
  [CompactSpace G]
  [AddCommGroup Wσ]
  [Module ℂ Wσ]
  [TopologicalSpace Wσ]
  {π : ContinuousRep G E}
  {K : Subgroup G}
  [CompactSpace K]
  {σ : ContinuousRep K Wσ} :
-- imply
  (IsotypicComponent π K σ).HasOrthogonalProjection := by
-- proof
  apply ContinuousRep.isotypicComponent_hasOrthogonalProjection π K σ


-- created on 2026-10-23
-- updated on 2026-10-24
