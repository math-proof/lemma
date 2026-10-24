import Mathlib
import sympy.Basic
open scoped TensorProduct
open Polynomial
open TensorProduct


private lemma Polynomial.nonempty_ringEquiv_tensor_quotient_span_singleton
  (κ : Type u₁) (D : Type u₂) [CommRing κ] [CommRing D] [Algebra κ D] (f : κ[X]) :
  Nonempty (D ⊗[κ] (κ[X] ⧸ Ideal.span {f}) ≃+* D[X] ⧸ Ideal.span {f.map (algebraMap κ D)}) := by
  let algXX : Algebra κ[X] D[X] := (mapRingHom (algebraMap κ D)).toAlgebra
  have halg : ∀ p : κ[X], algebraMap κ[X] D[X] p = p.map (algebraMap κ D) := fun _ => rfl
  have : IsScalarTower κ κ[X] D[X] := IsScalarTower.of_algebraMap_eq fun c => by
    rw [halg, Polynomial.algebraMap_apply, Polynomial.algebraMap_eq, Polynomial.map_C]
  let e₀ : D[X] ≃ₐ[κ] κ[X] ⊗[κ] D :=
    (polyEquivTensor κ D).trans (Algebra.TensorProduct.comm κ D κ[X])
  have he₀ : ∀ p : κ[X], e₀ (algebraMap κ[X] D[X] p) = algebraMap κ[X] (κ[X] ⊗[κ] D) p := by
    intro p
    rw [halg, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    change Algebra.TensorProduct.comm κ D κ[X] (polyEquivTensor κ D (p.map (algebraMap κ D))) = _
    have hF : (polyEquivTensor κ D).toAlgHom.toRingHom.comp (mapRingHom (algebraMap κ D)) =
        (Algebra.TensorProduct.includeRight (R := κ) (A := D) (B := κ[X])).toRingHom := by
      apply Polynomial.ringHom_ext
      ·
        intro c
        rw [RingHom.comp_apply, coe_mapRingHom, Polynomial.map_C, AlgHom.toRingHom_eq_coe,
          AlgHom.coe_toRingHom, AlgEquiv.coe_toAlgHom,
          ← Polynomial.algebraMap_apply, AlgEquiv.commutes, AlgHom.toRingHom_eq_coe,
          AlgHom.coe_toRingHom, Polynomial.C_eq_algebraMap, AlgHom.commutes]
      ·
        rw [RingHom.comp_apply, coe_mapRingHom, Polynomial.map_X, AlgHom.toRingHom_eq_coe,
          AlgHom.coe_toRingHom, AlgEquiv.coe_toAlgHom, polyEquivTensor_apply,
          eval₂_X]
        rfl
    have h1 : polyEquivTensor κ D (p.map (algebraMap κ D)) = (1 : D) ⊗ₜ[κ] p := by
      have := RingHom.congr_fun hF p
      simpa using this
    rw [h1]
    rfl
  let e₁ : D[X] ≃ₐ[κ[X]] κ[X] ⊗[κ] D := AlgEquiv.ofRingEquiv (f := e₀.toRingEquiv) he₀
  have hI : (Ideal.span {f}).map (algebraMap κ[X] D[X]) = Ideal.span {f.map (algebraMap κ D)} := by
    rw [Ideal.map_span, Set.image_singleton, halg]
  let e₂ : (D[X] ⧸ Ideal.span {f.map (algebraMap κ D)}) ≃+*
      D[X] ⊗[κ[X]] (κ[X] ⧸ Ideal.span {f}) :=
    (Ideal.quotEquivOfEq hI).symm.trans
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot D[X] (Ideal.span {f})).toRingEquiv
  let e₃ : D[X] ⊗[κ[X]] (κ[X] ⧸ Ideal.span {f}) ≃+* D ⊗[κ] (κ[X] ⧸ Ideal.span {f}) :=
    (Algebra.TensorProduct.comm κ[X] D[X] (κ[X] ⧸ Ideal.span {f})).toRingEquiv.trans <|
      ((Algebra.TensorProduct.congr (AlgEquiv.refl (R := κ[X]) (A₁ := κ[X] ⧸ Ideal.span {f})) e₁).toRingEquiv.trans <|
        ((Algebra.TensorProduct.cancelBaseChange κ κ[X] κ[X] (κ[X] ⧸ Ideal.span {f}) D).toRingEquiv.trans
          (Algebra.TensorProduct.comm κ (κ[X] ⧸ Ideal.span {f}) D).toRingEquiv))
  exact ⟨(e₂.trans e₃).symm⟩

universe u₁ u₂ in
/--
[Polynomial_nonempty_ringEquiv_tensor_quotient_span_singleton](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Polynomial_nonempty_ringEquiv_tensor_quotient_span_singleton.lean)
-/
@[path]
private lemma main
  {κ : Type u₁} [CommRing κ]
  {D : Type u₂} [CommRing D] [Algebra κ D]
  {f : κ[X]} :
-- imply
  Nonempty (D ⊗[κ] (κ[X] ⧸ Ideal.span {f}) ≃+* D[X] ⧸ Ideal.span {f.map (algebraMap κ D)}) :=
-- proof
  Polynomial.nonempty_ringEquiv_tensor_quotient_span_singleton κ D f


-- created on 2026-10-23
