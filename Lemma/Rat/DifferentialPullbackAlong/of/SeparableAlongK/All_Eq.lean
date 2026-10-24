import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_AlgebraicCurve_Correspondence
import Lemma.Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Lemma.Int.P2MUtil


namespace Definitions
end Definitions
open Definitions
open AlgebraicCurve AlgebraicCurve.Differential KaehlerDifferential TensorProduct
open Int


/--
[AlgebraicCurve_Differential_pullbackAlong_traceAlong_eq_traceAlong_pullbackAlong_of_algEquiv](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_Differential_pullbackAlong_traceAlong_eq_traceAlong_pullbackAlong_of_algEquiv.lean)
-/

private lemma  pullbackAlong_square
  [Field K]
  [Field F]
  [Field F']
  [Field F₀]
  [Field F₀']
  [Algebra K F]
  [Algebra K F']
  [Algebra K F₀]
  [Algebra K F₀']
  (φ' : F →ₐ[K] F') (φ : F₀ →ₐ[K] F₀') (θ : F →ₐ[K] F₀) (θ' : F' →ₐ[K] F₀')
  (hφ : ∀ x : F, θ' (φ' x) = φ (θ x)) (ω : Ω[F⁄K]) :
  pullbackAlong θ' (pullbackAlong φ' ω) = pullbackAlong φ (pullbackAlong θ ω) := by
  have key : ∀ ω ∈ Submodule.span F (Set.range (D K F)),
      pullbackAlong θ' (pullbackAlong φ' ω) = pullbackAlong φ (pullbackAlong θ ω) := by
    intro ω hω
    induction hω using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, rfl⟩ := hx
      rw [pullbackAlong_D, pullbackAlong_D, pullbackAlong_D, pullbackAlong_D, hφ]
    | zero => simp [map_zero]
    | add x y _ _ hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
    | smul a x _ hx =>
      rw [pullbackAlong_smul, pullbackAlong_smul, pullbackAlong_smul, pullbackAlong_smul, hx, hφ]
  refine key ω (by rw [KaehlerDifferential.span_range_derivation]; trivial)

private lemma  separableAlong_of_algEquiv
  [Field K]
  [Field F]
  [Field F']
  [Field F₀]
  [Field F₀']
  [Algebra K F]
  [Algebra K F']
  [Algebra K F₀]
  [Algebra K F₀']
  (φ' : F →ₐ[K] F') (φ : F₀ →ₐ[K] F₀') (θ : F ≃ₐ[K] F₀) (θ' : F' ≃ₐ[K] F₀')
  (hφ : ∀ x : F, θ' (φ' x) = φ (θ x)) (hsep : SeparableAlong K φ') : SeparableAlong K φ := by
  let := algebraAlong φ'
  let := algebraAlong φ
  have : Algebra.IsSeparable F F' := hsep
  exact Algebra.IsSeparable.of_equiv_equiv θ.toRingEquiv θ'.toRingEquiv (by ext x; exact (hφ x).symm)

private lemma  trace_of_algEquiv
  [Field K]
  [Field F]
  [Field F']
  [Field F₀]
  [Field F₀']
  [Algebra K F]
  [Algebra K F']
  [Algebra K F₀]
  [Algebra K F₀']
  (φ' : F →ₐ[K] F') (φ : F₀ →ₐ[K] F₀') (θ : F ≃ₐ[K] F₀) (θ' : F' ≃ₐ[K] F₀')
  (hφ : ∀ x : F, θ' (φ' x) = φ (θ x)) (u : F') :
  θ (let := algebraAlong φ'; Algebra.trace F F' u) = (let := algebraAlong φ; Algebra.trace F₀ F₀' (θ' u)) := by
  let := algebraAlong φ'
  let := algebraAlong φ
  have h := Algebra.trace_eq_of_equiv_equiv θ.toRingEquiv θ'.toRingEquiv (by ext x; exact (hφ x).symm) u
  rw [h]
  exact AlgEquiv.apply_symm_apply θ _

@[path]
private lemma main
  [Field K] [Field F] [Field F'] [Field F₀] [Field F₀'] [Algebra K F] [Algebra K F'] [Algebra K F₀] [Algebra K F₀']
  {φ' : F →ₐ[K] F'}
  {φ : F₀ →ₐ[K] F₀'}
  {η : Ω[F'⁄K]}
-- given
  (θ : F ≃ₐ[K] F₀)
  (θ' : F' ≃ₐ[K] F₀')
  (hφ : ∀ x : F, θ' (φ' x) = φ (θ x))
  (hsep : AlgebraicCurve.SeparableAlong K φ') :
-- imply
  AlgebraicCurve.Differential.pullbackAlong (θ : F →ₐ[K] F₀) (AlgebraicCurve.Differential.traceAlong φ' η) =
      AlgebraicCurve.Differential.traceAlong φ (AlgebraicCurve.Differential.pullbackAlong (θ' : F' →ₐ[K] F₀') η) := by
-- proof
  classical
    have hsep₀ : SeparableAlong K φ := separableAlong_of_algEquiv φ' φ θ θ' hφ hsep
    let := algebraAlong φ'
    have := isScalarTower_along φ'
    have : Algebra.IsSeparable F F' := hsep
    have : Algebra.FormallyEtale F F' := Algebra.FormallyEtale.of_isSeparable F F'
    let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K F F'
    obtain ⟨t, rfl⟩ := e.surjective η
    induction t using TensorProduct.inductionOn with
    | tmul u ω =>
      have he : e (u ⊗ₜ ω) = u • pullbackAlong φ' ω := by
        change KaehlerDifferential.mapBaseChange K F F' (u ⊗ₜ ω) = _
        rw [KaehlerDifferential.mapBaseChange_tmul]
        rfl
      rw [he, traceAlong_smul_pullbackAlong φ' hsep, pullbackAlong_smul, pullbackAlong_smul,
        pullbackAlong_square φ' φ (θ : F →ₐ[K] F₀) (θ' : F' →ₐ[K] F₀') hφ,
        traceAlong_smul_pullbackAlong φ hsep₀]
      congr 1
      exact trace_of_algEquiv φ' φ θ θ' hφ u
    | add x y hx hy => rw [map_add, map_add, map_add, map_add, map_add, hx, hy]


-- created on 2026-10-24
