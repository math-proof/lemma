import Mathlib
import sympy.Basic


namespace NoetherianModules

/--
[noetherian_iff_fg_modules_noetherian](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/NoetherianModules.lean)
-/
@[path]
private lemma noetherian_iff_fg_modules_noetherian
  {R : Type u}
  [CommRing R] :
-- imply
  IsNoetherianRing R ↔ ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M], IsNoetherian R M := by
-- proof
  constructor
  · intro h M _ _ _
    exact isNoetherian_of_isNoetherianRing_of_finite R M
  · intro h
    have : IsNoetherian R R := h R
    exact isNoetherianRing_iff.mpr this

end NoetherianModules

namespace NoetherianModules

/--
[finitePresentation_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/NoetherianModules.lean)
-/
@[path]
private lemma finitePresentation_iff
  {R M : Type*}
  [CommRing R]
  [AddCommGroup M]
  [Module R M] :
-- imply
  Module.FinitePresentation R M ↔ ∃ (n : ℕ) (f : (Fin n → R) →ₗ[R] M), Function.Surjective f ∧ (LinearMap.ker f).FG := by
-- proof
  constructor
  · intro h
    haveI : Module.Finite R M := inferInstance
    obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
    let e := (Finsupp.linearEquivFunOnFinite R R (Fin n)).symm
    let φ := (Finsupp.linearCombination R s).comp e.toLinearMap
    have hφ_surj : Function.Surjective φ := by
      intro m
      have hm : m ∈ Submodule.span R (Set.range s) := by rw [hs]; exact Submodule.mem_top
      rw [Submodule.mem_span_range_iff_exists_fun] at hm
      obtain ⟨c, hc⟩ := hm
      refine ⟨c, ?_⟩
      simp only [φ, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
      rw [show e c = Finsupp.equivFunOnFinite.symm c from rfl]
      rw [Finsupp.linearCombination_apply]
      rw [Finsupp.sum_fintype]
      · simp [Finsupp.equivFunOnFinite, hc]
      · intro i; simp
    have hφ_ker : (LinearMap.ker φ).FG :=
      Module.FinitePresentation.fg_ker φ hφ_surj
    exact ⟨n, φ, hφ_surj, hφ_ker⟩
  · intro ⟨n, f, hf_surj, hf_ker⟩
    exact Module.finitePresentation_of_surjective f hf_surj hf_ker

end NoetherianModules

namespace NoetherianModules

/--
[fg_module_finitely_presented](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/NoetherianModules.lean)
-/
@[path]
private lemma fg_module_finitely_presented
  {R M : Type*}
  [CommRing R]
  [AddCommGroup M]
  [Module R M]
  [IsNoetherianRing R]
  [Module.Finite R M] :
-- imply
  Module.FinitePresentation R M :=
-- proof
  Module.finitePresentation_of_finite R M

end NoetherianModules

namespace NoetherianModules

/--
[noetherian_ring_iff_acc](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/NoetherianModules.lean)
-/
@[path]
private lemma noetherian_ring_iff_acc
  {R : Type*}
  [CommRing R] :
-- imply
  IsNoetherianRing R ↔ ∀ f : ℕ →o Ideal R, ∃ n, ∀ m, n ≤ m → f n = f m := by
-- proof
  rwa [isNoetherianRing_iff]

end NoetherianModules

namespace NoetherianModules

/--
[surjective_hom_fg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/NoetherianModules.lean)
-/
@[path]
private lemma surjective_hom_fg
  [Ring R]
  [AddCommGroup M]
  [Module R M]
  [AddCommGroup N]
  [Module R N]
  {f : M →ₗ[R] N}
-- given
  (hf : Function.Surjective f) :
-- imply
  (Module.Finite R M → Module.Finite R N) ∧ (Module.Finite R N → (LinearMap.ker f).FG → Module.Finite R M) := by
-- proof
  constructor
  · intro hM
    exact Module.Finite.of_surjective f hf
  · intro hN hker
    rw [Module.finite_def]
    have h1 : (Submodule.map f ⊤).FG := by
      rwa [Submodule.map_top, LinearMap.range_eq_top.mpr hf]
    have h2 : (⊤ ⊓ LinearMap.ker f).FG := by
      rwa [top_inf_eq]
    exact Submodule.fg_of_fg_map_of_fg_inf_ker f h1 h2

end NoetherianModules


-- created on 2026-10-23
-- updated on 2026-10-24
