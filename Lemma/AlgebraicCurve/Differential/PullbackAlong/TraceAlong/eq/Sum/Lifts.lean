import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_AlgebraicCurve_Correspondence
import Lemma.Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Lemma.P2M.Util

open KaehlerDifferential TensorProduct
open AlgebraicCurve

/--
[AlgebraicCurve_Differential_pullbackAlong_traceAlong_eq_sum_lifts](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_Differential_pullbackAlong_traceAlong_eq_sum_lifts.lean)
-/

def liftsAlong
  {K F F' E : Type*}
  [Field K]
  [Field F]
  [Field F']
  [Field E]
  [Algebra K F]
  [Algebra K F']
  [Algebra K E]
  (φ : F →ₐ[K] F') (e : F →ₐ[K] E) : Set (F' →ₐ[K] E) := {σ | σ.comp φ = e}

private lemma  pullbackAlong_pullbackAlong
    {K F F' E : Type*}
    [Field K]
    [Field F]
    [Field F']
    [Field E]
    [Algebra K F]
    [Algebra K F']
    [Algebra K E]
    (ψ : F →ₐ[K] F') (σ : F' →ₐ[K] E) (ω : Ω[F⁄K]) :
    Differential.pullbackAlong σ (Differential.pullbackAlong ψ ω) =
      Differential.pullbackAlong (σ.comp ψ) ω := by
  have hmem : ω ∈ Submodule.span F (Set.range (D K F)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hmem using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨f, rfl⟩ := hx
      simp only [Differential.pullbackAlong_D, AlgHom.coe_comp, Function.comp_apply]
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx =>
      rw [Differential.pullbackAlong_smul, Differential.pullbackAlong_smul,
        Differential.pullbackAlong_smul, hx]
      rfl

private lemma  mem_liftsAlong
    {K F F' E : Type*}
    [Field K]
    [Field F]
    [Field F']
    [Field E]
    [Algebra K F]
    [Algebra K F']
    [Algebra K E]
    (φ : F →ₐ[K] F') (e : F →ₐ[K] E) (σ : F' →ₐ[K] E) :
    σ ∈ liftsAlong φ e ↔ σ.comp φ = e := Iff.rfl

private lemma  liftsAlong_eq_range
    {K F F' E : Type*}
    [Field K]
    [Field F]
    [Field F']
    [Field E]
    [Algebra K F]
    [Algebra K F']
    [Algebra K E]
    (φ : F →ₐ[K] F') (e : F →ₐ[K] E)
    [Algebra F F'] [IsScalarTower K F F'] [Algebra F E] [IsScalarTower K F E]
    (hφ : ∀ x, algebraMap F F' x = φ x) (he : ∀ x, algebraMap F E x = e x) :
    liftsAlong φ e = Set.range (fun τ : F' →ₐ[F] E => τ.restrictScalars K) := by
  ext σ
  constructor
  · intro hσ
    refine ⟨{ σ.toRingHom with commutes' := fun x => ?_ }, ?_⟩
    · simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
        MonoidHom.coe_coe, hφ, he]
      exact congrArg (fun g : F →ₐ[K] E => g x) hσ
    · ext x; rfl
  · rintro ⟨τ, rfl⟩
    show (τ.restrictScalars K).comp φ = e
    ext x
    simp only [AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply]
    rw [← hφ, τ.commutes, he]

private lemma  sum_eq_sum_algHom
    {K F F' E : Type*}
    [Field K]
    [Field F]
    [Field F']
    [Field E]
    [Algebra K F]
    [Algebra K F']
    [Algebra K E]
    (φ : F →ₐ[K] F') (e : F →ₐ[K] E)
    (S : Finset (F' →ₐ[K] E)) (hS : ∀ σ : F' →ₐ[K] E, σ ∈ S ↔ σ.comp φ = e)
    [Algebra F F'] [IsScalarTower K F F'] [Algebra F E] [IsScalarTower K F E]
    (hφ : ∀ x, algebraMap F F' x = φ x) (he : ∀ x, algebraMap F E x = e x)
    [Fintype (F' →ₐ[F] E)] {M : Type*} [AddCommMonoid M] (g : (F' →ₐ[K] E) → M) :
    ∑ σ ∈ S, g σ = ∑ τ : F' →ₐ[F] E, g (τ.restrictScalars K) := by
  classical
  have hset : S = Finset.univ.image (fun τ : F' →ₐ[F] E => τ.restrictScalars K) := by
    ext σ
    rw [hS, ← mem_liftsAlong, liftsAlong_eq_range φ e hφ he]
    simp only [Set.mem_range, Finset.mem_image, Finset.mem_univ, true_and]
  rw [hset, Finset.sum_image]
  intro τ₁ _ τ₂ _ h
  exact AlgHom.restrictScalars_injective K h

private lemma  pullbackAlong_traceAlong_eq_sum
    {K F F' E : Type*}
    [Field K]
    [Field F]
    [Field F']
    [Field E]
    [Algebra K F]
    [Algebra K F']
    [Algebra K E]
    [IsAlgClosed E] (φ : F →ₐ[K] F')
    (hfin : FiniteAlong K φ) (hsep : SeparableAlong K φ) (e : F →ₐ[K] E)
    (S : Finset (F' →ₐ[K] E)) (hS : ∀ σ : F' →ₐ[K] E, σ ∈ S ↔ σ.comp φ = e)
    (ω' : Ω[F'⁄K]) :
    Differential.pullbackAlong e (Differential.traceAlong φ ω') =
      ∑ σ ∈ S, Differential.pullbackAlong σ ω' := by
  let : Algebra F F' := algebraAlong φ
  have := isScalarTower_along φ
  let : Algebra F E := e.toRingHom.toAlgebra
  have : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq (fun x => (e.commutes x).symm)
  have : Module.Finite F F' := hfin
  have : Algebra.IsSeparable F F' := hsep
  have : Algebra.FormallyEtale F F' := Algebra.FormallyEtale.of_isSeparable F F'
  obtain ⟨t, rfl⟩ := (tensorKaehlerEquivOfFormallyEtale K F F').surjective ω'
  induction t using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy, Finset.sum_add_distrib]
  | tmul u ω =>
      have htm : (tensorKaehlerEquivOfFormallyEtale K F F') (u ⊗ₜ ω) =
          u • Differential.pullbackAlong φ ω := by
        rw [tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul]
        rfl
      rw [htm, Differential.traceAlong_smul_pullbackAlong φ hsep, Differential.pullbackAlong_smul]
      have hrhs : ∀ σ ∈ S,
          Differential.pullbackAlong σ (u • Differential.pullbackAlong φ ω) =
            σ u • Differential.pullbackAlong e ω := by
        intro σ hσ
        rw [Differential.pullbackAlong_smul, pullbackAlong_pullbackAlong, (hS σ).1 hσ]
      rw [Finset.sum_congr rfl hrhs, ← Finset.sum_smul,
        sum_eq_sum_algHom φ e S hS (fun _ => rfl) (fun _ => rfl) (fun σ => σ u)]
      congr 1
      have h := trace_eq_sum_embeddings E (K := F) (L := F') (x := u)
      simp only [AlgHom.coe_restrictScalars'] at h ⊢
      exact h




p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Differential_pullbackAlong_traceAlong_eq_sum_lifts.AlgebraicCurve"
@[path]
private lemma main
  [Field K] [Field F] [Field F'] [Field E] [Algebra K F] [Algebra K F'] [Algebra K E] [IsAlgClosed E]
  {φ : F →ₐ[K] F'}
  {e : F →ₐ[K] E}
  {S : Finset (F' →ₐ[K] E)}
  {ω' : Ω[F'⁄K]}
-- given
  (hfin : FiniteAlong K φ)
  (hsep : SeparableAlong K φ)
  (hS : ∀ σ : F' →ₐ[K] E, σ ∈ S ↔ σ.comp φ = e) :
-- imply
  Differential.pullbackAlong e (Differential.traceAlong φ ω') =
      ∑ σ ∈ S, Differential.pullbackAlong σ ω' :=
-- proof
  pullbackAlong_traceAlong_eq_sum φ hfin hsep e S hS ω'


-- created on 2026-10-23
