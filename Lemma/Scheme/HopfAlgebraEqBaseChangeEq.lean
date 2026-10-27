import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u v

private lemma tmul_one_injective
  {R : Type u} [CommRing R] [IsDomain R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  (M : Type v) [AddCommGroup M] [Module R M] [Module.Flat R M] :
  -- imply
  Function.Injective (fun y : M => TensorProduct.tmul R (1 : K) y) := by
  -- proof
  have h1 : Function.Injective ((Algebra.linearMap R K).rTensor M) := Module.Flat.rTensor_preserves_injective_linearMap _ (IsFractionRing.injective R K)
  intro a b hab
  have key : ((Algebra.linearMap R K).rTensor M) ((TensorProduct.lid R M).symm a) = ((Algebra.linearMap R K).rTensor M) ((TensorProduct.lid R M).symm b) := by
    simpa [LinearMap.rTensor_tmul] using hab
  refine (TensorProduct.lid R M).symm.injective (h1 key)

/--
[HopfAlgebra_eq_of_baseChange_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_HopfAlgebra_eq_of_baseChange_eq.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R] [IsDomain R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  {H : Type v} [CommRing H] [HopfAlgebra R H]
  {H' : Type v} [CommRing H'] [HopfAlgebra R H'] [Module.Flat R H']
  (φ ψ : BialgHom R H H')
  (h : (φ : AlgHom R H H').toLinearMap.baseChange K = (ψ : AlgHom R H H').toLinearMap.baseChange K) :
  -- imply
  φ = ψ := by
  -- proof
  refine DFunLike.ext _ _ fun x => ?_
  have hx := LinearMap.congr_fun h (TensorProduct.tmul R (1 : K) x)
  simp only [LinearMap.baseChange_tmul, AlgHom.toLinearMap_apply] at hx
  apply tmul_one_injective K H' hx


-- created on 2026-10-20
