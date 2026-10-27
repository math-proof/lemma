import Mathlib
import Initialize.Tactic.Attr.Basic


/--
[AlgebraicClosure_linearIndependent_of_linearIndependent_rat_of_forall_apply_smul](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicClosure_linearIndependent_of_linearIndependent_rat_of_forall_apply_smul.lean)
-/
@[path]
private lemma main
  {X : Type} [MulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) X]
  {ι : Type} {F : ι → X → AlgebraicClosure ℚ}
-- given
  (hF : ∀ (i : ι) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : X),
    F i (σ • x) = σ (F i x))
  (hind : LinearIndependent ℚ F) :
-- imply
  LinearIndependent (AlgebraicClosure ℚ) F := by
-- proof
  classical
  rw [linearIndependent_iff'] at hind ⊢
  intro s g hsum i hi
  set T : Set (AlgebraicClosure ℚ) := (↑(s.image g) : Set (AlgebraicClosure ℚ)) with hT
  have : Finite T := (s.image g).finite_toSet
  set E₀ : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.adjoin ℚ T with hE₀
  have : FiniteDimensional ℚ E₀ :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  set E : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.normalClosure ℚ E₀ (AlgebraicClosure ℚ) with hE
  have : FiniteDimensional ℚ E := normalClosure.is_finiteDimensional ℚ E₀ (AlgebraicClosure ℚ)
  have : IsGalois ℚ E := IsGalois.normalClosure ℚ E₀ (AlgebraicClosure ℚ)
  have hgE : ∀ j ∈ s, g j ∈ E := fun j hj =>
    IntermediateField.le_normalClosure E₀ (IntermediateField.subset_adjoin ℚ T
      (by rw [hT, Finset.coe_image]; apply Set.mem_image_of_mem g hj))
  let g' : ι → E := fun j => if h : g j ∈ E then ⟨g j, h⟩ else 0
  have hg' : ∀ j ∈ s, ((g' j : E) : AlgebraicClosure ℚ) = g j := by
    intro j hj
    simp only [g']
    rw [dite_eq_left (hgE j hj)]
  have hrel : ∀ (τ : E ≃ₐ[ℚ] E) (x : X),
      ∑ j ∈ s, ((τ (g' j) : E) : AlgebraicClosure ℚ) * F j x = 0 := by
    intro τ x
    obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure ℚ) τ
    have h0 := congrFun hsum (σ⁻¹ • x)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hF] at h0
    have h1 := congrArg σ h0
    rw [map_sum, map_zero] at h1
    rw [← h1]
    have key : ∀ y : E, ((AlgEquiv.restrictNormalHom E σ y : E) : AlgebraicClosure ℚ) = σ y :=
      fun y => AlgEquiv.restrictNormal_commutes σ E y
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [map_mul, key, hg' j hj, show σ (σ⁻¹ (F j x)) = F j x from σ.apply_symm_apply (F j x)]
  have htr : ∀ μ : E, ∑ j ∈ s, (Algebra.trace ℚ E (μ * g' j)) • F j = 0 := by
    intro μ
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply]
    have h2 : ∀ j ∈ s, (Algebra.trace ℚ E (μ * g' j)) • F j x =
        ∑ τ : E ≃ₐ[ℚ] E, ((τ μ : E) : AlgebraicClosure ℚ) *
          (((τ (g' j) : E) : AlgebraicClosure ℚ) * F j x) := by
      intro j _
      rw [Algebra.smul_def, IsScalarTower.algebraMap_apply ℚ E (AlgebraicClosure ℚ),
        trace_eq_sum_automorphisms, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [map_mul, ← mul_assoc]
      rfl
    rw [Finset.sum_congr rfl h2, Finset.sum_comm]
    refine Finset.sum_eq_zero fun τ _ => ?_
    rw [← Finset.mul_sum, hrel τ x, mul_zero]
  have htr0 : ∀ μ : E, ∀ j ∈ s, Algebra.trace ℚ E (μ * g' j) = 0 := fun μ => hind s _ (htr μ)
  have hg'0 : g' i = 0 := by
    refine (traceForm_nondegenerate ℚ E).1 (g' i) fun μ => ?_
    rw [Algebra.traceForm_apply, mul_comm]
    exact htr0 μ i hi
  rw [← hg' i hi, hg'0]
  rfl


-- created on 2026-10-13
