import Mathlib.SetTheory.Cardinal.Finite
import Lemma.Definitions.Def_ModularCurve_ComplexPlaceDictionary
import Lemma.Definitions.Def_ModularForm_HeckeOperator

set_option autoImplicit false

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups Topology

namespace ModularCurve

structure UniformizedHeckeCurve (Γ : Subgroup (GL (Fin 2) ℝ)) (Fc : Type) [Field Fc] [Algebra ℂ Fc] where

  pt : ℍ → AlgebraicCurve.Place ℂ Fc

  realize : Fc → ℍ → ℂ

  ramification : ℍ → ℕ

  ramification_pos : ∀ τ : ℍ, 0 < ramification τ

  mem_pt_iff : ∀ (τ : ℍ) (x : Fc), x ∈ (pt τ).toValuationSubring ↔
      Filter.IsBoundedUnder (· ≤ ·) (𝓝[≠] τ) (fun z : ℍ => ‖realize x z‖)

  meromorphicOrderAt_realize : ∀ (τ : ℍ) (x : Fc), x ≠ 0 →
      meromorphicOrderAt (fun z : ℂ => realize x (ofComplex z)) (τ : ℂ) =
        (((ramification τ : ℤ) * (pt τ).ord x : ℤ) : WithTop ℤ)

  pt_eq_pt_iff : ∀ τ τ' : ℍ, pt τ = pt τ' ↔ ∃ γ ∈ Γ, γ • τ = τ'

  distinguished : Fc

  exists_pt_eq : ∀ P : AlgebraicCurve.Place ℂ Fc, distinguished ∈ P.toValuationSubring → ∃ τ : ℍ, pt τ = P

  two_mul_ramification : ∀ τ : ℍ, 2 * ramification τ = Nat.card (MulAction.stabilizer Γ τ)

  heckePoints : ∀ ℓ : ℕ, ℓ.Prime → Multiset (GL (Fin 2) ℝ)

  corr : ∀ ℓ : ℕ, ℓ.Prime → (AlgebraicCurve.Divisor ℂ Fc →+ AlgebraicCurve.Divisor ℂ Fc)

  corr_single_pt : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (τ : ℍ),
      corr ℓ hℓ (Finsupp.single (pt τ) 1) =
        ((heckePoints ℓ hℓ).map fun δ => Finsupp.single (pt (δ • τ)) 1).sum

section Level

variable (N : ℕ)

def gamma0GL : Subgroup (GL (Fin 2) ℝ) :=
  (CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)

def heckePoints (ℓ : ℕ) (_hℓ : ℓ.Prime) : Multiset (GL (Fin 2) ℝ) :=
  (Finset.range ℓ).val.map (fun j => ModularForm.heckeMatrix ℓ j) +
    (if ℓ ∣ N then 0 else {ModularForm.heckeDiagMatrix ℓ})

end Level

end ModularCurve

end
