import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[IntermediateField_cofinal_comp_fixingSubgroupEquiv_symm](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IntermediateField_cofinal_comp_fixingSubgroupEquiv_symm.lean)
-/
@[path]
private lemma main
  {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
  (L : IntermediateField K Ω) [FiniteDimensional K L]
  (r : (AlgEquiv K Ω Ω) →* (AlgEquiv ℚ (AlgebraicClosure ℚ) (AlgebraicClosure ℚ)))
  -- given
  (hlevel : ∀ E : IntermediateField K Ω, FiniteDimensional K E → ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧ ∀ σ : AlgEquiv K Ω Ω, r σ ∈ F.fixingSubgroup → σ ∈ E.fixingSubgroup)
  (hopen : ∀ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F → ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧ ∀ σ : AlgEquiv K Ω Ω, σ ∈ E.fixingSubgroup → r σ ∈ F.fixingSubgroup) :
  -- imply
  (∀ E : IntermediateField L Ω, FiniteDimensional L E → ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧ ∀ τ : AlgEquiv L Ω Ω, (r.comp (L.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv L).symm.toMonoidHom)) τ ∈ F.fixingSubgroup → τ ∈ E.fixingSubgroup) ∧ (∀ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F → ∃ E : IntermediateField L Ω, FiniteDimensional L E ∧ ∀ τ : AlgEquiv L Ω Ω, τ ∈ E.fixingSubgroup → (r.comp (L.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv L).symm.toMonoidHom)) τ ∈ F.fixingSubgroup) := by
  -- proof
  classical
  have hj : ∀ (τ : AlgEquiv L Ω Ω) (x : Ω), ((L.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv L).symm.toMonoidHom) τ) x = τ x := fun _ _ => rfl
  refine ⟨fun E hE => ?_, fun F hF => ?_⟩
  ·
    let _ := hE
    let _ : FiniteDimensional K (E.restrictScalars K) := by
      show FiniteDimensional K E
      apply FiniteDimensional.trans K L E
    obtain ⟨F, hF, h⟩ := hlevel (E.restrictScalars K) inferInstance
    refine ⟨F, hF, fun τ hτ => ?_⟩
    have hσ := h _ hτ
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
    intro x hx
    rw [← hj τ x]
    apply hσ x (by rwa [IntermediateField.mem_restrictScalars])
  ·
    obtain ⟨E₀, hE₀, h⟩ := hopen F hF
    let _ := hE₀
    let _ : FiniteDimensional K (L ⊔ E₀ : IntermediateField K Ω) := IntermediateField.finiteDimensional_sup L E₀
    have hK : Module.Finite K (IntermediateField.extendScalars (le_sup_left : L ≤ L ⊔ E₀)) := by
      change Module.Finite K (L ⊔ E₀ : IntermediateField K Ω)
      infer_instance
    refine ⟨IntermediateField.extendScalars (le_sup_left : L ≤ L ⊔ E₀), Module.Finite.of_restrictScalars_finite K L _, fun τ hτ => ?_⟩
    apply h
    rw [IntermediateField.mem_fixingSubgroup_iff] at hτ ⊢
    intro x hx
    rw [hj]
    apply hτ x ((IntermediateField.mem_extendScalars _).mpr ((le_sup_right : E₀ ≤ L ⊔ E₀) hx))


-- created on 2026-10-20
