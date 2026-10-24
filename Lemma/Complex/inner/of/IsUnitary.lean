import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.LieGroups.code.KFiniteProps
open ContinuousRep
open scoped ComplexOrder


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
  have : (ContinuousLinearMap.adjoint (π.toMonoidHom g) * π.toMonoidHom g) v = v := by
    rw [h]; simp
  rwa [ContinuousLinearMap.mul_apply] at this

/--
[unitary_orthogonal_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma unitary_orthogonal_invariant
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
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
  rw [← ContinuousLinearMap.adjoint_inner_right, unitary_adjoint_eq_inv π hU]
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
  (orthogonalProjection_intertwines_subrep π hU K W₁ W₂ hW₁ hW₂).toContinuousLinearMap v = W₂.orthogonalProjection (v : E) := by
-- proof
  simp only [orthogonalProjection_intertwines_subrep, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply]

/--
[continuous_inverse_of_bijective_clm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma continuous_inverse_of_bijective_clm
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
  [NormedAddCommGroup E]
  [InnerProductSpace ℂ E]
  [CompleteSpace E]
  [IsTopologicalGroup G]
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
  [NormedAddCommGroup E]
  [InnerProductSpace ℂ E]
  [CompleteSpace E]
  [IsTopologicalGroup G]
  [Group G']
  [TopologicalSpace G']
  [NormedAddCommGroup V₁]
  [NormedSpace ℂ V₁]
  [CompleteSpace V₁]
  [NormedAddCommGroup V₂]
  [NormedSpace ℂ V₂]
  [CompleteSpace V₂]
  {π₁ : ContinuousRep G' V₁}
  {π₂ : ContinuousRep G' V₂}
  {T : RepHom π₁ π₂}
-- given
  (hbij : Function.Bijective T.toContinuousLinearMap) :
-- imply
  Nonempty (RepEquiv π₁ π₂) := by
-- proof
  let f := T.toContinuousLinearMap
  let linEquiv : V₁ ≃ₗ[ℂ] V₂ := LinearEquiv.ofBijective f.toLinearMap hbij
  let cle : V₁ ≃L[ℂ] V₂ :=
    { linEquiv with
      continuous_toFun := f.continuous
      continuous_invFun := continuous_inverse_of_bijective_clm f hbij }
  exact ⟨{
    toContinuousLinearEquiv := cle
    intertwines := by
      intro g
      ext v
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
      have hT := ContinuousLinearMap.ext_iff.mp (T.intertwines g) v
      simp only [ContinuousLinearMap.comp_apply] at hT
      exact hT
  }⟩

/--
[repEquiv_trans](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma repEquiv_trans
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
  [NormedAddCommGroup E]
  [InnerProductSpace ℂ E]
  [CompleteSpace E]
  [IsTopologicalGroup G]
  [Group G']
  [TopologicalSpace G']
  [AddCommGroup V₁]
  [Module ℂ V₁]
  [TopologicalSpace V₁]
  [AddCommGroup V₂]
  [Module ℂ V₂]
  [TopologicalSpace V₂]
  [AddCommGroup V₃]
  [Module ℂ V₃]
  [TopologicalSpace V₃]
  {π₁ : ContinuousRep G' V₁}
  {π₂ : ContinuousRep G' V₂}
  {π₃ : ContinuousRep G' V₃}
-- given
  (h₁ : Nonempty (RepEquiv π₁ π₂))
  (h₂ : Nonempty (RepEquiv π₂ π₃)) :
-- imply
  Nonempty (RepEquiv π₁ π₃) := by
-- proof
  obtain ⟨e₁⟩ := h₁
  obtain ⟨e₂⟩ := h₂
  exact ⟨{
    toContinuousLinearEquiv := e₁.toContinuousLinearEquiv.trans e₂.toContinuousLinearEquiv
    intertwines := by
      intro g
      ext v
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.trans_apply]
      have h1 := ContinuousLinearMap.ext_iff.mp (e₁.intertwines g) v
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe] at h1
      rw [h1]
      have h2 := ContinuousLinearMap.ext_iff.mp (e₂.intertwines g) (e₁.toContinuousLinearEquiv v)
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe] at h2
      exact h2
  }⟩

/--
[repEquiv_symm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma repEquiv_symm
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
  [NormedAddCommGroup E]
  [InnerProductSpace ℂ E]
  [CompleteSpace E]
  [IsTopologicalGroup G]
  [Group G']
  [TopologicalSpace G']
  [AddCommGroup V₁]
  [Module ℂ V₁]
  [TopologicalSpace V₁]
  [AddCommGroup V₂]
  [Module ℂ V₂]
  [TopologicalSpace V₂]
  {π₁ : ContinuousRep G' V₁}
  {π₂ : ContinuousRep G' V₂}
-- given
  (h : Nonempty (RepEquiv π₁ π₂)) :
-- imply
  Nonempty (RepEquiv π₂ π₁) := by
-- proof
  obtain ⟨e⟩ := h
  exact ⟨{
    toContinuousLinearEquiv := e.toContinuousLinearEquiv.symm
    intertwines := by
      intro g
      ext w
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
      have hg := ContinuousLinearMap.ext_iff.mp (e.intertwines g)
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe] at hg
      apply e.toContinuousLinearEquiv.injective
      simp only [ContinuousLinearEquiv.apply_symm_apply]
      rw [hg (e.toContinuousLinearEquiv.symm w)]
      simp only [ContinuousLinearEquiv.apply_symm_apply]
  }⟩

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
    have hTval := orthogonalProjection_intertwines_subrep_val π hU K W₁ W₂ hW₁ hW₂ ⟨v, hv⟩
    have hTzero : T.toContinuousLinearMap ⟨v, hv⟩ = 0 := by
      change (orthogonalProjection_intertwines_subrep π hU K W₁ W₂ hW₁ hW₂).toContinuousLinearMap
        ⟨v, hv⟩ = 0
      rw [show (orthogonalProjection_intertwines_subrep π hU K W₁ W₂ hW₁ hW₂).toContinuousLinearMap
        = T.toContinuousLinearMap from rfl, hzero]
      rfl
    rw [hTval] at hTzero
    exact (Submodule.orthogonalProjection_eq_zero_iff).mp hTzero
  ·
    exfalso
    apply hne
    have h12 := @repEquiv_of_bijective_repHom _ _ _
      _ _ _ (hW₁.isClosed.completeSpace_coe)
      _ _ _ (hW₂.isClosed.completeSpace_coe)
      ((π.restrictSubgroup K).subrepresentation W₁ hW₁)
      ((π.restrictSubgroup K).subrepresentation W₂ hW₂) T hbij
    exact repEquiv_trans (repEquiv_trans (repEquiv_symm hiso₁) h12) hiso₂

/--
[mem_orthogonal_sSup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma mem_orthogonal_sSup
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
  [NormedAddCommGroup E]
  [InnerProductSpace ℂ E]
  [CompleteSpace E]
  [IsTopologicalGroup G]
  [NormedAddCommGroup F]
  [InnerProductSpace ℂ F]
  {T : Set (Submodule ℂ F)}
  {v : F}
-- given
  (h : ∀ W ∈ T, v ∈ Wᗮ) :
-- imply
  v ∈ (sSup T)ᗮ := by
-- proof
  rw [Submodule.mem_orthogonal']
  intro w hw
  have key : sSup T ≤ (Submodule.span ℂ ({v} : Set F))ᗮ := by
    apply sSup_le
    intro W hW w' hw'
    rw [Submodule.mem_orthogonal']
    intro u hu
    rw [Submodule.mem_span_singleton] at hu
    obtain ⟨c, rfl⟩ := hu
    rw [inner_smul_right]
    have hv : ∀ u ∈ W, @inner ℂ _ _ v u = 0 :=
      (Submodule.mem_orthogonal' W v).mp (h W hW)
    rw [inner_eq_zero_symm.mp (hv w' hw')]
    ring
  have hw2 := key hw
  have hw3 : ∀ u ∈ Submodule.span ℂ ({v} : Set F), @inner ℂ _ _ w u = 0 :=
    (Submodule.mem_orthogonal' _ w).mp hw2
  rw [inner_eq_zero_symm]
  exact hw3 v (Submodule.mem_span_singleton_self v)

/--
[sSup_orthogonal_sSup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma sSup_orthogonal_sSup
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
  [NormedAddCommGroup E]
  [InnerProductSpace ℂ E]
  [CompleteSpace E]
  [IsTopologicalGroup G]
  [NormedAddCommGroup F]
  [InnerProductSpace ℂ F]
  {S T : Set (Submodule ℂ F)}
-- given
  (h : ∀ U ∈ S, ∀ W ∈ T, U.IsOrtho W) :
-- imply
  (sSup S).IsOrtho (sSup T) := by
-- proof
  rw [Submodule.IsOrtho]
  apply sSup_le
  intro U hU v hv
  exact mem_orthogonal_sSup T v (fun W hW => h U hU W hW hv)

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
  exact irreducible_subspaces_orthogonal π hU K σ τ W₁ W₂
    hW₁inv hW₂inv hirr₁ hirr₂ hiso₁ hiso₂ hne

/--
[discreteMeasureRep_extends](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma discreteMeasureRep_extends
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
  {V : Type uG}
  [NormedAddCommGroup V]
  [NormedSpace ℂ V]
  {π : G →* (V →L[ℂ] V)}
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
  {V : Type uG}
  [NormedAddCommGroup V]
  [NormedSpace ℂ V]
  {π : G →* (V →L[ℂ] V)}
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
  have := (MonoidAlgebra.lift ℂ (V →L[ℂ] V) G).apply_symm_apply φ
  rwa [key] at this

/--
[total_variation_eval_cont](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma total_variation_eval_cont
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
  {V : Type uG}
  [NormedAddCommGroup V]
  [NormedSpace ℂ V]
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
  {M : Type uM}
  [Ring M]
  [Algebra ℂ M]
  [TopologicalSpace M]
  [inst : CompactlySupportedMeasureAlgebra G M]
  {f : G → ℝ}
-- given
  (hf : Continuous f)
  (hf_nn : ∀ g, 0 ≤ f g) :
-- imply
  @Continuous (MonoidAlgebra ℂ G) ℝ (TopologicalSpace.induced (MonoidAlgebra.lift ℂ M G inst.dirac) ‹TopologicalSpace M›) inferInstance (fun μ => μ.sum (fun g c => ‖c‖ * f g)) :=
-- proof
  inst.total_variation_cont f hf hf_nn

/--
[rep_lift_opNorm_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma rep_lift_opNorm_le
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
  {V : Type uG}
  [NormedAddCommGroup V]
  [NormedSpace ℂ V]
  [Group G]
  [NormedAddCommGroup V]
  [NormedSpace ℂ V]
  {π : G →* (V →L[ℂ] V)}
  {μ : MonoidAlgebra ℂ G} :
-- imply
  ‖(MonoidAlgebra.lift ℂ (V →L[ℂ] V) G π) μ‖ ≤ μ.sum (fun g c => ‖c‖ * ‖π g‖) := by
-- proof
  rw [MonoidAlgebra.lift_apply]
  calc ‖μ.sum (fun g c => c • π g)‖
    ≤ μ.support.sum (fun g => ‖μ g • π g‖) := norm_sum_le _ _
    _ = μ.support.sum (fun g => ‖μ g‖ * ‖π g‖) := by
      congr 1; ext g; exact norm_smul (μ g) (π g)
    _ = μ.sum (fun g c => ‖c‖ * ‖π g‖) := rfl
set_option checkBinderAnnotations false in

/--
[total_variation_eval_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma total_variation_eval_continuous
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
  {V : Type uG}
  [NormedAddCommGroup V]
  [NormedSpace ℂ V]
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
  {M : Type uM}
  [Ring M]
  [Algebra ℂ M]
  [TopologicalSpace M]
  [CompactlySupportedMeasureAlgebra G M]
  {f : G → ℝ}
-- given
  (hf : Continuous f)
  (hf_nn : ∀ g, 0 ≤ f g) :
-- imply
  @Continuous (MonoidAlgebra ℂ G) ℝ (TopologicalSpace.induced (MonoidAlgebra.lift ℂ M G CompactlySupportedMeasureAlgebra.dirac) ‹TopologicalSpace M›) inferInstance (fun μ => μ.sum (fun g c => ‖c‖ * f g)) :=
-- proof
  total_variation_eval_cont f hf hf_nn

/--
[rep_continuous_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma rep_continuous_theorem
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
  {V : Type uG}
  [NormedAddCommGroup V]
  [NormedSpace ℂ V]
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
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
  {π : G →* (V →L[ℂ] V)}
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
    topologicalAddGroup_induced δ_lift
  let π_lift := MonoidAlgebra.lift ℂ (V →L[ℂ] V) G π
  change @Continuous _ _ t_ind _ π_lift
  have h_tendsto : Filter.Tendsto π_lift (@nhds _ t_ind 0) (nhds 0) := by
    apply squeeze_zero_norm (fun μ => rep_lift_opNorm_le π μ)
    rw [← show (0 : MonoidAlgebra ℂ G).sum (fun g c => ‖c‖ * ‖(π g : V →L[ℂ] V)‖) = 0 from
      Finsupp.sum_zero_index]
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
  {V : Type uG}
  [NormedAddCommGroup V]
  [NormedSpace ℂ V]
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
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
  {V : Type uG}
  [NormedAddCommGroup V]
  [NormedSpace ℂ V]
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
  {M : Type uM}
  [Ring M]
  [Algebra ℂ M]
  [TopologicalSpace M]
  [inst : CompactlySupportedMeasureAlgebra G M]
  [FrechetUrysohnSpace M] :
-- imply
  Dense (Set.range (MonoidAlgebra.lift ℂ M G inst.dirac)) := by
-- proof
  rw [dense_iff_closure_eq]
  ext x
  simp only [Set.mem_univ, iff_true]
  exact seqClosure_subset_closure (discrete_measures_sequentially_dense x)

/--
[blt_alg_hom_extend](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma blt_alg_hom_extend
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
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
  refine ⟨{ toFun := g_fun,
    map_one' := ?_,
    map_mul' := ?_,
    map_zero' := ?_,
    map_add' := ?_,
    commutes' := ?_ }, hg_cont, hg_ext⟩
  · have h1 : (1 : β) = ι 1 := (map_one ι).symm
    rw [h1, hg_ext, map_one]
  · intro x y
    have key : (fun p : β × β => g_fun (p.1 * p.2)) =
      (fun p : β × β => g_fun p.1 * g_fun p.2) := by
      apply @Continuous.ext_on γ (β × β) _ _ _ (Set.range ι ×ˢ Set.range ι)
      · exact h_dense.prod h_dense
      · exact hg_cont.comp (continuous_fst.mul continuous_snd)
      · exact (hg_cont.comp continuous_fst).mul (hg_cont.comp continuous_snd)
      · rintro ⟨b₁, b₂⟩ ⟨⟨a₁, rfl⟩, ⟨a₂, rfl⟩⟩
        show g_fun (ι a₁ * ι a₂) = g_fun (ι a₁) * g_fun (ι a₂)
        rw [← map_mul ι, hg_ext, hg_ext, hg_ext, map_mul]
    exact congr_fun key (x, y)
  · have h0 : (0 : β) = ι 0 := (map_zero ι).symm
    rw [h0, hg_ext, map_zero]
  · intro x y
    have key : (fun p : β × β => g_fun (p.1 + p.2)) =
      (fun p : β × β => g_fun p.1 + g_fun p.2) := by
      apply @Continuous.ext_on γ (β × β) _ _ _ (Set.range ι ×ˢ Set.range ι)
      · exact h_dense.prod h_dense
      · exact hg_cont.comp (continuous_fst.add continuous_snd)
      · exact (hg_cont.comp continuous_fst).add (hg_cont.comp continuous_snd)
      · rintro ⟨b₁, b₂⟩ ⟨⟨a₁, rfl⟩, ⟨a₂, rfl⟩⟩
        show g_fun (ι a₁ + ι a₂) = g_fun (ι a₁) + g_fun (ι a₂)
        rw [← map_add ι, hg_ext, hg_ext, hg_ext, map_add]
    exact congr_fun key (x, y)
  · intro r
    have : algebraMap ℂ β r = ι (algebraMap ℂ α r) := (ι.commutes r).symm
    rw [this, hg_ext, f.commutes]

/--
[CompactlySupportedMeasureAlgebra.alg_hom_extend](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma CompactlySupportedMeasureAlgebra.alg_hom_extend
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
  {V : Type uG}
  [NormedAddCommGroup V]
  [NormedSpace ℂ V]
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
  {M : Type uM}
  [Ring M]
  [Algebra ℂ M]
  [TopologicalSpace M]
  [ContinuousAdd M]
  [ContinuousMul M]
  [inst : CompactlySupportedMeasureAlgebra G M]
  [Ring A]
  [Algebra ℂ A]
  [inst_top_A : TopologicalSpace A]
  [inst_unif_A : UniformSpace A]
  [CompleteSpace A]
  [T2Space A]
  [ContinuousAdd A]
  [ContinuousMul A]
  [IsUniformAddGroup A]
  {f : MonoidAlgebra ℂ G →ₐ[ℂ] A}
-- given
  (h_dense : Dense (Set.range (MonoidAlgebra.lift ℂ M G inst.dirac)))
  (h_cont : @Continuous (MonoidAlgebra ℂ G) A (TopologicalSpace.induced (MonoidAlgebra.lift ℂ M G inst.dirac) ‹TopologicalSpace M›) inst_top_A f)
  (h_top_eq : inst_top_A = inst_unif_A.toTopologicalSpace := by rfl) :
-- imply
  ∃ (g : M →ₐ[ℂ] A), Continuous g ∧ ∀ μ : MonoidAlgebra ℂ G, g ((MonoidAlgebra.lift ℂ M G inst.dirac) μ) = f μ := by
-- proof
  subst h_top_eq
  letI : TopologicalSpace (MonoidAlgebra ℂ G) :=
    TopologicalSpace.induced (MonoidAlgebra.lift ℂ M G inst.dirac) ‹TopologicalSpace M›
  have di : IsDenseInducing (MonoidAlgebra.lift ℂ M G inst.dirac : MonoidAlgebra ℂ G → M) := {
    eq_induced := rfl
    dense := h_dense
  }
  let g_fun := di.extend (f : MonoidAlgebra ℂ G → A)
  have hg_ext : ∀ x, g_fun ((MonoidAlgebra.lift ℂ M G inst.dirac) x) = f x :=
    IsDenseInducing.extend_eq di h_cont
  have h_filter : ∀ b : M, ∃ c : A,
    Filter.Tendsto (f : MonoidAlgebra ℂ G → A) (Filter.comap
      (MonoidAlgebra.lift ℂ M G inst.dirac : MonoidAlgebra ℂ G → M) (nhds b)) (nhds c) := by
    intro b
    set ι := (MonoidAlgebra.lift ℂ M G inst.dirac : MonoidAlgebra ℂ G → M)
    haveI : ContinuousNeg M := IsSemitopologicalSemiring.continuousNeg_of_mul
    haveI : IsTopologicalAddGroup M := ⟨⟩
    haveI : IsTopologicalAddGroup (MonoidAlgebra ℂ G) :=
      Topology.IsInducing.topologicalAddGroup
        (f := (MonoidAlgebra.lift ℂ M G inst.dirac).toAddMonoidHom') di.toIsInducing
    letI uM : UniformSpace M := IsTopologicalAddGroup.rightUniformSpace M
    haveI : IsUniformAddGroup M := isUniformAddGroup_of_addCommGroup
    letI uS : UniformSpace (MonoidAlgebra ℂ G) :=
      IsTopologicalAddGroup.rightUniformSpace (MonoidAlgebra ℂ G)
    haveI : IsUniformAddGroup (MonoidAlgebra ℂ G) := isUniformAddGroup_of_addCommGroup
    have hι_ui : IsUniformInducing ι :=
      AddMonoidHom.isUniformInducing_of_isInducing
        (f := (MonoidAlgebra.lift ℂ M G inst.dirac).toAddMonoidHom') di.toIsInducing
    have hf_uc : UniformContinuous (f : MonoidAlgebra ℂ G → A) :=
      uniformContinuous_addMonoidHom_of_continuous (hom := MonoidAlgebra ℂ G →+ A)
        (f := f.toAddMonoidHom') h_cont
    exact uniformly_extend_exists hι_ui di.dense hf_uc b
  have hg_cont : Continuous g_fun := di.continuous_extend h_filter
  exact blt_alg_hom_extend (MonoidAlgebra.lift ℂ M G inst.dirac) f h_dense g_fun hg_cont hg_ext

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
  [Ring M]
  [Algebra ℂ M]
  [TopologicalSpace M]
  [ContinuousAdd M]
  [ContinuousMul M]
  [CompactlySupportedMeasureAlgebra G M]
  [FrechetUrysohnSpace M]
  [FiniteDimensional ℂ V]
  {π : G →* (V →L[ℂ] V)}
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
  {π : G →* (V →L[ℂ] V)}
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
  {π : G →* (V →L[ℂ] V)}
  [FiniteDimensional ℂ V]
-- given
  (hcont : Continuous (fun p : G × V => (π p.1) p.2)) :
-- imply
  letI := weakTopologyOnDiscreteMeasures (G := G) (M := M) Continuous (fun p : MonoidAlgebra ℂ G × V => (discreteMeasureRep π p.1) p.2) := by
-- proof
  letI : TopologicalSpace (MonoidAlgebra ℂ G) :=
    weakTopologyOnDiscreteMeasures (G := G) (M := M)
  have h_rep_cont := discreteMeasureRep_continuous_to_opnorm (M := M) π hcont
  exact (h_rep_cont.comp continuous_fst).clm_apply continuous_snd

/--
[discreteMeasureRep_BLT_extension](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma discreteMeasureRep_BLT_extension
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
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
  {π : G →* (V →L[ℂ] V)}
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
    (discreteMeasureRep π) h_dense h_weak_cont

/--
[measureRep_exists_extension](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma measureRep_exists_extension
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
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
  {π : G →* (V →L[ℂ] V)}
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
  {π : G →* (V →L[ℂ] V)}
  [FiniteDimensional ℂ V]
  {π_ext : M →ₐ[ℂ] (V →L[ℂ] V)}
-- given
  (hcont : Continuous (fun p : G × V => (π p.1) p.2))
  (h_extends : ∀ g : G, π_ext (CompactlySupportedMeasureAlgebra.dirac g) = π g)
  (hcont_ext : Continuous π_ext) :
-- imply
  Continuous (fun p : M × V => (π_ext p.1) p.2) :=
-- proof
(isBoundedBilinearMap_apply (𝕜 := ℂ)).continuous.comp (hcont_ext.prodMap continuous_id)

/--
[measureRep_continuous_extension](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma measureRep_continuous_extension
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
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
  {π : G →* (V →L[ℂ] V)}
  [FiniteDimensional ℂ V]
-- given
  (hcont : Continuous (fun p : G × V => (π p.1) p.2)) :
-- imply
  ∃ (π_ext : M →ₐ[ℂ] (V →L[ℂ] V)), (∀ g : G, π_ext (CompactlySupportedMeasureAlgebra.dirac g) = π g) ∧ Continuous π_ext ∧ Continuous (fun p : M × V => (π_ext p.1) p.2) := by
-- proof
  obtain ⟨π_ext, hcont_ext, h_dirac, _h_extends⟩ := measureRep_exists_extension (M := M) π hcont
  exact ⟨π_ext, h_dirac, hcont_ext,
    measureRep_continuous_bilinear (M := M) π hcont π_ext h_dirac hcont_ext⟩

/--
[measureRep_unique_extension](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma measureRep_unique_extension
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
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
  {π : G →* (V →L[ℂ] V)}
  [CompleteSpace V]
  {φ₁ φ₂ : M →ₐ[ℂ] (V →L[ℂ] V)}
-- given
  (hcont : Continuous (fun p : G × V => (π p.1) p.2))
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
  have h : (IsotypicComponent π K σ).orthogonalProjection
    (↑((IsotypicComponent π K σ).orthogonalProjection v)) =
    (IsotypicComponent π K σ).orthogonalProjection v :=
    Submodule.orthogonalProjection_mem_subspace_eq_self _
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
    exact ((IsotypicComponent π K σ).orthogonalProjection w).2
  · intro hv
    refine ⟨v, ?_⟩
    change (isotypicProjection π K σ) v = v
    rw [isotypicProjection]
    simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
    have : (IsotypicComponent π K σ).orthogonalProjection v = ⟨v, hv⟩ :=
      Submodule.orthogonalProjection_mem_subspace_eq_self ⟨v, hv⟩
    rw [this]

/--
[kFiniteSubspace_stable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean)
-/
@[path]
private lemma kFiniteSubspace_stable_eq
  {G : Type uG}
  [Group G]
  [TopologicalSpace G]
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
