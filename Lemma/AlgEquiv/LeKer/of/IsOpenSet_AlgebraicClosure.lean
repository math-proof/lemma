import Mathlib
import sympy.Basic


private lemma exists_numberField_ker_restrictNormalHom_le
  (L₁ L₂ : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L₁] [FiniteDimensional ℚ L₂] :
  ∃ (F : Type) (_ : Field F) (_ : NumberField F) (_ : IsGalois ℚ F)
    (_ : Algebra F (AlgebraicClosure ℚ)) (_ : IsScalarTower ℚ F (AlgebraicClosure ℚ)),
    ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ ∈ (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker →
      (∀ x ∈ L₁, σ x = x) ∧ (∀ x ∈ L₂, σ x = x) := by
  have : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  have : Normal ℚ (AlgebraicClosure ℚ) :=
    normal_iff.mpr fun x =>
      ⟨(Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).isIntegral, IsAlgClosed.splits _⟩
  let E : IntermediateField ℚ (AlgebraicClosure ℚ) := L₁ ⊔ L₂
  have : FiniteDimensional ℚ E := IntermediateField.finiteDimensional_sup L₁ L₂
  let Fi : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.normalClosure ℚ E (AlgebraicClosure ℚ)
  have hfd : FiniteDimensional ℚ Fi := normalClosure.is_finiteDimensional ℚ E (AlgebraicClosure ℚ)
  have hn : Normal ℚ Fi := normalClosure.normal ℚ E (AlgebraicClosure ℚ)
  have : Algebra.IsSeparable ℚ Fi := Algebra.IsSeparable.of_integral ℚ Fi
  have hg : IsGalois ℚ Fi := IsGalois.mk
  have hE : E ≤ Fi := IntermediateField.le_normalClosure E
  have hinst : (Fi.algebra : Algebra ℚ Fi) = (DivisionRing.toRatAlgebra : Algebra ℚ Fi) :=
    Subsingleton.elim _ _
  refine ⟨Fi, inferInstance, ?_, ?_, inferInstance, ?_, ?_⟩
  · exact { to_charZero := inferInstance, to_finiteDimensional := hinst ▸ hfd }
  · exact hinst ▸ hg
  · exact hinst ▸ (inferInstance : IsScalarTower ℚ Fi (AlgebraicClosure ℚ))
  ·
    intro σ hσ
    have h1 : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) Fi) σ = 1 :=
      MonoidHom.mem_ker.mp hσ
    have hfix : ∀ x : AlgebraicClosure ℚ, x ∈ Fi → σ x = x := by
      intro x hx
      have h2 := AlgEquiv.restrictNormal_commutes σ Fi ⟨x, hx⟩
      change (AlgEquiv.restrictNormalHom Fi σ) = 1 at h1
      rw [show σ.restrictNormal Fi = AlgEquiv.restrictNormalHom Fi σ from rfl, h1] at h2
      simpa using h2.symm
    exact ⟨fun x hx => hfix x (hE ((le_sup_left : L₁ ≤ E) hx)),
      fun x hx => hfix x (hE ((le_sup_right : L₂ ≤ E) hx))⟩

private lemma exists_finiteDimensional_fixingSubgroup_le
  {H : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}
  (hH : IsOpen (H : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))) :
  ∃ E : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ E ∧
    ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ E, σ x = x) → σ ∈ H := by
  obtain ⟨E, hE, hEH⟩ := (krullTopology_mem_nhds_one_iff ℚ (AlgebraicClosure ℚ) H).mp (hH.mem_nhds H.one_mem)
  refine ⟨E, hE, fun σ hσ => hEH ?_⟩
  exact (IntermediateField.mem_fixingSubgroup_iff E σ).mpr fun x hx => hσ x hx
/--
[IsOpen_exists_numberField_ker_restrictNormalHom_le](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsOpen_exists_numberField_ker_restrictNormalHom_le.lean)
-/
@[path]
private lemma main
  {H : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}
-- given
  (hH : IsOpen (H : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))) :
-- imply
  ∃ (F : Type) (_ : Field F) (_ : NumberField F) (_ : IsGalois ℚ F)
    (_ : Algebra F (AlgebraicClosure ℚ)) (_ : IsScalarTower ℚ F (AlgebraicClosure ℚ)),
    (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker ≤ H := by
  -- proof
    obtain ⟨E, hE, hEH⟩ := exists_finiteDimensional_fixingSubgroup_le hH
    have := hE
    obtain ⟨F, iF, iNF, iG, iA, iT, hF⟩ := exists_numberField_ker_restrictNormalHom_le E E
    exact ⟨F, iF, iNF, iG, iA, iT, fun σ hσ => hEH σ (hF σ hσ).1⟩


-- created on 2026-10-23
