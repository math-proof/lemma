import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.LieGroups.code.HarishChandraCorollaries


/--
[corollary_14_5](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HarishChandraCorollaries.lean)
-/
@[path]
private lemma corollary_14_5
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  [LieAlgebra.IsSemisimple ℂ 𝔤]
  [Module.Finite ℂ 𝔤]
  {Δ : TriangularDecomposition ℂ 𝔤}
  {M : LieBimodule.{_, _, u_hc_bim} ℂ 𝔤}
-- given
  (hirr : M.IsIrreducible)
  (hlocfin : IsHarishChandraBimodule M) :
-- imply
  (∃ (χ : ↥(Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ 𝔤)) →ₐ[ℂ] ℂ) (V : Type u_hc_bim) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : LieRingModule 𝔤 V) (_ : LieModule ℂ 𝔤 V) (_ : Module.Finite ℂ V) (_ : LieModule.IsIrreducible ℂ 𝔤 V), ∃ (surj : TensorProduct ℂ V (MaximalQuotient χ) →ₗ[ℂ] M.carrier), Function.Surjective surj ∧ (∀ (x : 𝔤) (t : TensorProduct ℂ V (MaximalQuotient χ)), surj ((tensorBimodule (LieBimodule.trivial V) χ).adjointAction x t) = M.adjointAction x (surj t))) ∧ (∀ (W : Type 0) [AddCommGroup W] [Module ℂ W] [LieRingModule 𝔤 W] [LieModule ℂ 𝔤 W] [Module.Finite ℂ W] (_ : LieModule.IsIrreducible ℂ 𝔤 W), Module.Finite ℂ (HomAdEquivariant W M)) := by
-- proof
  have part_i := corollary_14_5_i M hirr hlocfin
  refine ⟨part_i, ?_⟩
  obtain ⟨χ, V₀, instACG, instMod, instLRM, instLM, instFin, hirr_V₀, surj, hsurj, hequivar⟩ := part_i
  have hAdm : IsAdmissibleBimodule (tensorBimodule (LieBimodule.trivial V₀) χ) :=
    corollary_14_4 Δ (LieBimodule.trivial V₀) χ
  exact hc_quotient_admissible (tensorBimodule (LieBimodule.trivial V₀) χ) M hAdm surj hsurj hequivar


-- created on 2026-10-23
-- updated on 2026-10-24
