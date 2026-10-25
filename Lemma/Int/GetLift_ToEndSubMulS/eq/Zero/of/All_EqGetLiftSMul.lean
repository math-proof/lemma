import Mathlib
import sympy.Basic
import Def.v1.Atlas.LieGroups.code.PrincipalSeries.Part6


/--
[commutator_acts_zero_when_scalar](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PrincipalSeries.lean)
-/
@[path]
private lemma commutator_acts_zero_when_scalar
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {z x : UniversalEnvelopingAlgebra R 𝔤}
  {V : Type u_mod}
  [AddCommGroup V]
  [Module R V]
  [LieRingModule 𝔤 V]
  [LieModule R 𝔤 V]
  {_ : LieModule.IsIrreducible R 𝔤 V}
  {_ : Module.Finite R V}
-- given
  (hz : ∀ (V : Type u_mod) [AddCommGroup V] [Module R V] [LieRingModule 𝔤 V] [LieModule R 𝔤 V] (_ : LieModule.IsIrreducible R 𝔤 V) (_ : Module.Finite R V), ∃ (c : R), ∀ (v : V), (UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 V)) z v = c • v) :
-- imply
  ∀ (v : V), (UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 V)) (x * z - z * x) v = 0 := by
-- proof
  intro v
  obtain ⟨c, hc⟩ := hz V ‹_› ‹_›
  set φ := UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 V)
  have h1 : (φ (x * z - z * x) : Module.End R V) = φ x * φ z - φ z * φ x := by
    rw [map_sub, map_mul, map_mul]
  change (φ (x * z - z * x)) v = 0
  rw [h1]
  show (φ x) ((φ z) v) - (φ z) ((φ x) v) = 0
  rw [hc v, hc ((φ x) v), map_smul]
  exact sub_self _

/--
[functor_H_lambda_on_dual_verma_aux](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PrincipalSeries.lean)
-/
@[path]
private lemma functor_H_lambda_on_dual_verma_aux
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {wt_lambda : Δ.𝔥 →ₗ[R] R}
  {H : FunctorHLambda Δ wt_lambda}
  {wt_mu : Δ.𝔥 →ₗ[R] R}
  {M_mu : Type*}
  [AddCommGroup M_mu]
  [Module R M_mu]
  [LieRingModule 𝔤 M_mu]
  [LieModule R 𝔤 M_mu]
-- given
  (hM_mu : IsVermaModule Δ M_mu wt_mu) :
-- imply
  ∃ (P : PrincipalSeriesBimodule Δ), P.wt_lambda = wt_lambda ∧ P.wt_mu = wt_mu := by
-- proof
  obtain ⟨M₁, inst₁, inst₂, inst₃, inst₄, ⟨hV₁⟩⟩ := verma_module_exists Δ wt_lambda
  obtain ⟨M₂, inst₅, inst₆, inst₇, inst₈, ⟨hV₂⟩⟩ := verma_module_exists Δ wt_mu
  exact ⟨{ wt_lambda := wt_lambda
    wt_mu := wt_mu
    M_source := M₁
    M_target := M₂
    verma_source := hV₁
    verma_target := hV₂ }, rfl, rfl⟩

/--
[functor_H_lambda_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PrincipalSeries.lean)
-/
@[path]
private lemma functor_H_lambda_injective
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {wt_lambda : Δ.𝔥 →ₗ[R] R}
  {H : FunctorHLambda.{u_mod} Δ wt_lambda}
  {X₁ X₂ : Type u_mod}
  [AddCommGroup X₁]
  [Module R X₁]
  [LieRingModule 𝔤 X₁]
  [LieModule R 𝔤 X₁]
  [AddCommGroup X₂]
  [Module R X₂]
  [LieRingModule 𝔤 X₂]
  [LieModule R 𝔤 X₂]
  {f : X₁ →ₗ⁅R, 𝔤⁆ X₂}
-- given
  (hf_inj : Function.Injective f)
  (h₁ : H.onObject X₁)
  (hfh₁ : ∀ (m : H.M_lambda), f (h₁.val m) = 0) :
-- imply
  h₁.val = 0 := by
-- proof
  ext m
  have hfm : f (h₁.val m) = 0 := hfh₁ m
  exact hf_inj (hfm.trans (map_zero f).symm)

/--
[functor_H_lambda_middle_exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PrincipalSeries.lean)
-/
@[path]
private lemma functor_H_lambda_middle_exact
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {wt_lambda : Δ.𝔥 →ₗ[R] R}
  {H : FunctorHLambda.{u_mod} Δ wt_lambda}
  {X₁ X₂ X₃ : Type u_mod}
  [AddCommGroup X₁]
  [Module R X₁]
  [LieRingModule 𝔤 X₁]
  [LieModule R 𝔤 X₁]
  [AddCommGroup X₂]
  [Module R X₂]
  [LieRingModule 𝔤 X₂]
  [LieModule R 𝔤 X₂]
  [AddCommGroup X₃]
  [Module R X₃]
  [LieRingModule 𝔤 X₃]
  [LieModule R 𝔤 X₃]
  {f : X₁ →ₗ⁅R, 𝔤⁆ X₂}
  {g : X₂ →ₗ⁅R, 𝔤⁆ X₃}
-- given
  (hf_inj : Function.Injective f)
  (h_exact : f.range = g.ker)
  (h₂ : H.onObject X₂) :
-- imply
  (∀ (m : H.M_lambda), g (h₂.val m) = 0) ↔ ∃ (h₁ : H.onObject X₁), ∀ (m : H.M_lambda), f (h₁.val m) = h₂.val m := by
-- proof
  constructor
  · intro hg_zero
    have h_in_ker : ∀ (m : H.M_lambda), h₂.val m ∈ g.ker := by
      intro m
      exact LieModuleHom.mem_ker.mpr (hg_zero m)
    have h_in_range : ∀ (m : H.M_lambda), h₂.val m ∈ f.range := by
      intro m
      rw [h_exact]; exact h_in_ker m
    let f_lin : X₁ →ₗ[R] X₂ := ↑f
    have hf_lin_inj : Function.Injective f_lin := hf_inj
    have h_preimage : ∀ (m : H.M_lambda), ∃ (x : X₁), f x = h₂.val m := by
      intro m
      exact (LieModuleHom.mem_range f (h₂.val m)).mp (h_in_range m)
    let h₁_fun : H.M_lambda → X₁ := fun m => (h_preimage m).choose
    have h₁_spec : ∀ m, f (h₁_fun m) = h₂.val m := by
      intro m; exact (h_preimage m).choose_spec
    have h₁_linear : ∀ (m₁ m₂ : H.M_lambda), h₁_fun (m₁ + m₂) = h₁_fun m₁ + h₁_fun m₂ := by
      intro m₁ m₂
      apply hf_inj
      simp [h₁_spec, map_add]
    have h₁_smul : ∀ (r : R) (m : H.M_lambda), h₁_fun (r • m) = r • h₁_fun m := by
      intro r m
      apply hf_inj
      simp [h₁_spec, map_smul]
    have h₁_lie : ∀ (x : 𝔤) (m : H.M_lambda), h₁_fun (⁅x, m⁆) = ⁅x, h₁_fun m⁆ := by
      intro x m
      apply hf_inj
      rw [h₁_spec, LieModuleHom.map_lie f x (h₁_fun m), h₁_spec]
      exact LieModuleHom.map_lie h₂.val x m
    let h₁_lm : H.M_lambda →ₗ⁅R, 𝔤⁆ X₁ :=
      { toFun := h₁_fun
        map_add' := h₁_linear
        map_smul' := h₁_smul
        map_lie' := fun {x m} => h₁_lie x m }
    have h₁_lf : IsLocallyFiniteMap R (h₁_lm : H.M_lambda →ₗ[R] X₁) := by
      have h_comp : f_lin.comp (h₁_lm : H.M_lambda →ₗ[R] X₁) =
        (h₂.val : H.M_lambda →ₗ[R] X₂) := by
        ext m
        exact h₁_spec m
      have h_map_range : Submodule.map f_lin
        (LinearMap.range (h₁_lm : H.M_lambda →ₗ[R] X₁)) =
        LinearMap.range (h₂.val : H.M_lambda →ₗ[R] X₂) := by
        rw [← LinearMap.range_comp, h_comp]
      exact Submodule.fg_of_fg_map_injective f_lin hf_lin_inj (h_map_range ▸ h₂.property)
    exact ⟨⟨h₁_lm, h₁_lf⟩, h₁_spec⟩
  · intro ⟨h₁, hh₁⟩ m
    rw [← hh₁ m]
    have hmem : f (h₁.val m) ∈ f.range := ⟨h₁.val m, rfl⟩
    rw [h_exact] at hmem
    exact LieModuleHom.mem_ker.mp hmem


-- created on 2026-10-23
-- updated on 2026-10-24
