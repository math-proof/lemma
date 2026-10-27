import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped TensorProduct
open Polynomial
open TensorProduct


private lemma Polynomial.isDomain_tensor_of_isFractionRing
  (F₀ : Type u₁) (κ : Type u₂) (k : Type u₃) [Field F₀] [CommRing κ] [Field k]
  [Algebra F₀[X] κ] [IsFractionRing F₀[X] κ] [Algebra F₀ κ] [IsScalarTower F₀ F₀[X] κ]
  [Algebra F₀ k] : IsDomain (κ ⊗[F₀] k) := by
  have eS : F₀[X] ⊗[F₀] k ≃+* k[X] :=
    ((Algebra.TensorProduct.comm F₀ F₀[X] k).trans (polyEquivTensor F₀ k).symm).toRingEquiv
  have : IsDomain (F₀[X] ⊗[F₀] k) := MulEquiv.isDomain k[X] eS.toMulEquiv
  have hinj : Function.Injective (algebraMap F₀[X] (F₀[X] ⊗[F₀] k)) := by
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap F₀ k)
      (LinearMap.ker_eq_bot.mpr (algebraMap F₀ k).injective)
    intro x y hxy
    have h := congrArg (TensorProduct.rid F₀ F₀[X] ∘ LinearMap.lTensor F₀[X] g) hxy
    simp only [Function.comp_apply, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, LinearMap.lTensor_tmul, TensorProduct.rid_tmul] at h
    have hg1 : g 1 = 1 := by
      have := LinearMap.congr_fun hg (1 : F₀)
      simpa using this
    simpa [hg1] using h
  have hle : Algebra.algebraMapSubmonoid (F₀[X] ⊗[F₀] k) (nonZeroDivisors F₀[X]) ≤
      nonZeroDivisors (F₀[X] ⊗[F₀] k) := by
    rintro _ ⟨m, hm, rfl⟩
    apply mem_nonZeroDivisors_of_ne_zero
    intro h0
    apply nonZeroDivisors.ne_zero hm
    exact hinj (h0.trans (map_zero _).symm)
  have := IsLocalization.tensor (R := F₀[X]) (S := F₀[X] ⊗[F₀] k) κ (nonZeroDivisors F₀[X])
  have hD := IsLocalization.isDomain_of_le_nonZeroDivisors ((F₀[X] ⊗[F₀] k) ⊗[F₀[X]] κ) hle
  have : IsScalarTower F₀[X] F₀[X] κ := IsScalarTower.left _
  have e : (F₀[X] ⊗[F₀] k) ⊗[F₀[X]] κ ≃+* κ ⊗[F₀] k :=
    (Algebra.TensorProduct.comm F₀[X] (F₀[X] ⊗[F₀] k) κ).toRingEquiv.trans
      (Algebra.TensorProduct.cancelBaseChange F₀ F₀[X] F₀[X] κ k).toRingEquiv
  refine @MulEquiv.isDomain _ ((F₀[X] ⊗[F₀] k) ⊗[F₀[X]] κ) _ _ hD e.symm.toMulEquiv

universe u₁ u₂ u₃ in
/--
[Polynomial_isDomain_tensor_of_isFractionRing](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Polynomial_isDomain_tensor_of_isFractionRing.lean)
-/
@[path]
private lemma main
  {F₀ : Type u₁} [Field F₀]
  {κ : Type u₂} [CommRing κ] [Algebra F₀[X] κ] [IsFractionRing F₀[X] κ] [Algebra F₀ κ] [IsScalarTower F₀ F₀[X] κ]
  {k : Type u₃} [Field k] [Algebra F₀ k] :
-- imply
  IsDomain (κ ⊗[F₀] k) :=
-- proof
  Polynomial.isDomain_tensor_of_isFractionRing F₀ κ k


-- created on 2026-10-23
