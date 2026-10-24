import Mathlib
import Lemma.Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option autoImplicit false

namespace CerednikDrinfeld

namespace SpecialFormal

namespace ModuliPackage

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O]

structure Hom (G H : ModuliPackage.{0, 0} p O) where

  app : ∀ (B : Type) [CommRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)), G.obj B ψ hB → H.obj B ψ hB

  naturality : ∀ {B B' : Type} [CommRing B] [CommRing B'] {ψ : O →+* B} {ψ' : O →+* B'}
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →+* B') (hf : f.comp ψ = ψ')
    (x : G.obj B ψ hB), app B' ψ' hB' (G.map hB hB' f hf x) = H.map hB hB' f hf (app B ψ hB x)

def IsLimitPreserving (F : ModuliPackage.{0, 0} p O) : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra O B] (hB : IsNilpotent (p : B)),
    (∀ x : F.obj B (algebraMap O B) hB,
      ∃ (B₀ : Type) (_ : CommRing B₀) (_ : Algebra O B₀) (_ : Algebra.FinitePresentation O B₀)
        (hB₀ : IsNilpotent (p : B₀)) (g : B₀ →ₐ[O] B) (x₀ : F.obj B₀ (algebraMap O B₀) hB₀),
        F.map hB₀ hB (g : B₀ →+* B) (g.comp_algebraMap) x₀ = x) ∧
    (∀ (B₀ : Type) [CommRing B₀] [Algebra O B₀] [Algebra.FinitePresentation O B₀]
      (hB₀ : IsNilpotent (p : B₀)) (g : B₀ →ₐ[O] B) (x₀ x₀' : F.obj B₀ (algebraMap O B₀) hB₀),
      F.map hB₀ hB (g : B₀ →+* B) (g.comp_algebraMap) x₀ = F.map hB₀ hB (g : B₀ →+* B) (g.comp_algebraMap) x₀' →
      ∃ (B₁ : Type) (_ : CommRing B₁) (_ : Algebra O B₁) (_ : Algebra.FinitePresentation O B₁)
        (hB₁ : IsNilpotent (p : B₁)) (g₁ : B₀ →ₐ[O] B₁) (h : B₁ →ₐ[O] B) (_ : h.comp g₁ = g),
        F.map hB₀ hB₁ (g₁ : B₀ →+* B₁) (g₁.comp_algebraMap) x₀ =
          F.map hB₀ hB₁ (g₁ : B₀ →+* B₁) (g₁.comp_algebraMap) x₀')

def IsEffective (F : ModuliPackage.{0, 0} p O) : Prop :=
  ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] (ψ : O →+* A) (hA : IsNilpotent (p : A))
    (hAn : ∀ n : ℕ, IsNilpotent ((p : A ⧸ IsLocalRing.maximalIdeal A ^ (n + 1)))),
    (∀ x x' : F.obj A ψ hA,
      (∀ n : ℕ, F.map hA (hAn n) (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ (n + 1))) rfl x =
        F.map hA (hAn n) (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ (n + 1))) rfl x') → x = x') ∧
    (∀ y : ∀ n : ℕ, F.obj (A ⧸ IsLocalRing.maximalIdeal A ^ (n + 1))
        ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ (n + 1))).comp ψ) (hAn n),
      (∀ n : ℕ, F.map (hAn (n + 1)) (hAn n)
          (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))) (by
            ext a; rfl) (y (n + 1)) = y n) →
      ∃ x : F.obj A ψ hA, ∀ n : ℕ,
        F.map hA (hAn n) (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ (n + 1))) rfl x = y n)

open scoped TensorProduct in

def IsCompletionSheaf (F : ModuliPackage.{0, 0} p O) : Prop :=
  ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B))
    (hBc : IsNilpotent (p : AdicCompletion (IsLocalRing.maximalIdeal B) B))
    (hBcc : IsNilpotent (p : (AdicCompletion (IsLocalRing.maximalIdeal B) B) ⊗[B]
      (AdicCompletion (IsLocalRing.maximalIdeal B) B))),
    (∀ x x' : F.obj B ψ hB,
      F.map hB hBc (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B)) rfl x =
        F.map hB hBc (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B)) rfl x' → x = x') ∧
    (∀ z : F.obj (AdicCompletion (IsLocalRing.maximalIdeal B) B)
        ((algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B)).comp ψ) hBc,
      F.map (ψ' := (algebraMap B ((AdicCompletion (IsLocalRing.maximalIdeal B) B) ⊗[B]
          (AdicCompletion (IsLocalRing.maximalIdeal B) B))).comp ψ) hBc hBcc
          ((Algebra.TensorProduct.includeLeft :
            AdicCompletion (IsLocalRing.maximalIdeal B) B →ₐ[B]
              (AdicCompletion (IsLocalRing.maximalIdeal B) B) ⊗[B] (AdicCompletion (IsLocalRing.maximalIdeal B) B)) :
            AdicCompletion (IsLocalRing.maximalIdeal B) B →+* _)
          (by ext b; simp [RingHom.comp_apply, Algebra.TensorProduct.algebraMap_apply]) z =
        F.map (ψ' := (algebraMap B ((AdicCompletion (IsLocalRing.maximalIdeal B) B) ⊗[B]
          (AdicCompletion (IsLocalRing.maximalIdeal B) B))).comp ψ) hBc hBcc
          ((Algebra.TensorProduct.includeRight :
            AdicCompletion (IsLocalRing.maximalIdeal B) B →ₐ[B]
              (AdicCompletion (IsLocalRing.maximalIdeal B) B) ⊗[B] (AdicCompletion (IsLocalRing.maximalIdeal B) B)) :
            AdicCompletion (IsLocalRing.maximalIdeal B) B →+* _)
          (by ext b; simp [RingHom.comp_apply, Algebra.TensorProduct.algebraMap_apply,
            Algebra.TensorProduct.tmul_one_eq_one_tmul]) z →
      ∃ x : F.obj B ψ hB,
        F.map hB hBc (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B)) rfl x = z)

end ModuliPackage

end SpecialFormal

end CerednikDrinfeld
