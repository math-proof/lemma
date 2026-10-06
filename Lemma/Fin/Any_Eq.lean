import Mathlib
import sympy.Basic

open UpperHalfPlane
open scoped MatrixGroups

/--
[ModularForm_exists_coe_eq_of_levelOne](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularForm_exists_coe_eq_of_levelOne.lean)
-/
@[main]
private lemma main
  {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)}
  {k : ℤ}
  {F : ModularForm 𝒮ℒ k} :
-- imply
  ∃ G : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k, (G : ℍ → ℂ) = (F : ℍ → ℂ) := by
-- proof
  have hle : ((Γ : Subgroup (GL (Fin 2) ℝ))) ≤ 𝒮ℒ := by
    rintro _ ⟨γ, -, rfl⟩
    exact ⟨γ, rfl⟩
  refine ⟨{ toFun := F
            slash_action_eq' := fun γ hγ => F.slash_action_eq' γ (hle hγ)
            holo' := F.holo'
            bdd_at_cusps' := fun hc => F.bdd_at_cusps' (hc.mono hle) }, rfl⟩


-- created on 2026-10-05
