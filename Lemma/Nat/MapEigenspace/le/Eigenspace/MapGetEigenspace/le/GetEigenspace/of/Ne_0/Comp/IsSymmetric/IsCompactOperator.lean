import Mathlib
import sympy.Basic

open Module.End
open scoped InnerProductSpace

/--
[ContinuousLinearMap_map_eigenspace_orthogonal_le_of_commute](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ContinuousLinearMap_map_eigenspace_orthogonal_le_of_commute.lean)
-/
@[main]
private lemma main
  {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  {T : E →L[𝕜] E}
  {S : E →L[𝕜] E}
  {μ : 𝕜}
-- given
  (_hT : IsCompactOperator T)
  (hT' : (T : E →ₗ[𝕜] E).IsSymmetric)
  (hST : S.comp T = T.comp S)
  (_hμ : μ ≠ 0) :
-- imply
  (eigenspace (T : Module.End 𝕜 E) μ).map (S : Module.End 𝕜 E) ≤ eigenspace (T : Module.End 𝕜 E) μ ∧
    ((eigenspace (T : Module.End 𝕜 E) μ)ᗮ).map (S : Module.End 𝕜 E) ≤ (eigenspace (T : Module.End 𝕜 E) μ)ᗮ := by
-- proof
  have hTsa : IsSelfAdjoint T := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mpr hT'
  have hadj : ContinuousLinearMap.adjoint T = T := hTsa.adjoint_eq
  have hST' : (ContinuousLinearMap.adjoint S).comp T = T.comp (ContinuousLinearMap.adjoint S) := by
    have h := congrArg ContinuousLinearMap.adjoint hST
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, hadj] at h
    exact h.symm

  have hpres : ∀ R : E →L[𝕜] E, R.comp T = T.comp R →
      ∀ v ∈ eigenspace (T : Module.End 𝕜 E) μ, R v ∈ eigenspace (T : Module.End 𝕜 E) μ := by
    intro R hR v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    have hv' : T v = μ • v := hv
    show T (R v) = μ • R v
    have h := congrArg (fun f : E →L[𝕜] E => f v) hR
    simp only [ContinuousLinearMap.comp_apply] at h
    rw [← h, hv', map_smul]
  refine ⟨?_, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact hpres S hST v hv
  · rintro _ ⟨v, hv, rfl⟩
    rw [Submodule.mem_orthogonal]
    intro e he
    show ⟪e, S v⟫_𝕜 = 0
    rw [← ContinuousLinearMap.adjoint_inner_left]
    exact (Submodule.mem_orthogonal _ _).mp hv _ (hpres _ hST' e he)


-- created on 2026-10-05
