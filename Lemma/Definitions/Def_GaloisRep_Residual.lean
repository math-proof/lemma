import Lemma.Definitions.Def_EllipticCurve_FrobeniusTrace
import Lemma.Definitions.Def_FLTPrelim_Modularity
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.FieldTheory.Finiteness

set_option autoImplicit false

noncomputable section

open scoped WeierstrassCurve.Affine TensorProduct
open Polynomial

def GaloisFactorsThroughFiniteLevel {M : Type} [MulOneClass M]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* M) : Prop :=
  ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
    ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ x = x) → ρ σ = 1

structure ResidualGaloisRep (k : Type) [Field k] : Type 1 where

  V : Type
  [instAddCommGroup : AddCommGroup V]
  [instModule : Module k V]

  finrank_eq : Module.finrank k V = 2

  ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End k V

  factorsThroughFiniteLevel : GaloisFactorsThroughFiniteLevel ρ

attribute [instance] ResidualGaloisRep.instAddCommGroup ResidualGaloisRep.instModule

instance ResidualGaloisRep.instModuleFinite {k : Type} [Field k] (ρ : ResidualGaloisRep k) :
    Module.Finite k ρ.V :=
  Module.finite_of_finrank_eq_succ ρ.finrank_eq

namespace ResidualGaloisRep

variable {k : Type} [Field k]

def IsUnramifiedAt (ρ : ResidualGaloisRep k) (q : ℕ) : Prop :=
  ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q →
    ∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ.ρ σ = 1

def IsAttachedTo (ρ : ResidualGaloisRep k) {N : ℕ}
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (φ : integralClosure ℤ ℂ →+* k) : Prop :=
  ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → (ℓ : k) ≠ 0 →
    ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
        ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f ℓ ∧
          LinearMap.charpoly (ρ.ρ σ) = X ^ 2 - C (φ a) * X + C ((ℓ : k))

def IsOdd (ρ : ResidualGaloisRep k) : Prop :=
  ∀ c : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, c * c = 1 → c ≠ 1 →
    LinearMap.det (ρ.ρ c) = -1

def IsIrreducible (ρ : ResidualGaloisRep k) : Prop :=
  ∀ W : Submodule k ρ.V, (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
    ∀ x ∈ W, ρ.ρ σ x ∈ W) → W = ⊥ ∨ W = ⊤

abbrev baseChange (k' : Type) [Field k'] [Algebra k k'] (ρ : ResidualGaloisRep k) :
    ResidualGaloisRep k' :=
  { V := k' ⊗[k] ρ.V
    finrank_eq := by rw [Module.finrank_baseChange, ρ.finrank_eq]
    ρ := { toFun := fun σ => (ρ.ρ σ).baseChange k'
           map_one' := by rw [map_one, LinearMap.baseChange_one]
           map_mul' := fun σ τ => by rw [map_mul, LinearMap.baseChange_mul] }
    factorsThroughFiniteLevel := by
      obtain ⟨L, hL, h1⟩ := ρ.factorsThroughFiniteLevel
      exact ⟨L, hL, fun σ hσ => by
        rw [MonoidHom.coe_mk, OneHom.coe_mk, h1 σ hσ, LinearMap.baseChange_one]⟩ }

def baseChangeAlong {k' : Type} [Field k'] (φ : k →+* k') (ρ : ResidualGaloisRep k) :
    ResidualGaloisRep k' :=
  letI : Algebra k k' := φ.toAlgebra
  ρ.baseChange k'

def IsAbsolutelyIrreducible (ρ : ResidualGaloisRep k) : Prop :=
  (ρ.baseChange (AlgebraicClosure k)).IsIrreducible

end ResidualGaloisRep

def WeierstrassCurve.residualGaloisRepOf (W : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime]
    (hcard : Nat.card (Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ W p)) :
    ResidualGaloisRep (ZMod p) :=
  haveI hfin : Finite (Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point p) :=
    Nat.finite_of_card_ne_zero
      (hcard ▸ pow_ne_zero 2 (Fact.out (p := p.Prime)).pos.ne')
  { V := Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point p
    finrank_eq := by
      have hp : p.Prime := Fact.out
      have h := Module.natCard_eq_pow_finrank (K := ZMod p)
        (V := Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point p)
      rw [hcard, Nat.card_zmod] at h
      exact (Nat.pow_right_injective hp.two_le h).symm
    ρ := WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ W p
    factorsThroughFiniteLevel := hker }

end
