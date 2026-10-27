import Lemma.EllipticCurve.FrobeniusTrace
import Def.FLTPrelim_Modularity
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.FieldTheory.Finiteness
import Structure.GaloisRep_Residual
import Abbrev.GaloisRep_Residual

set_option autoImplicit false

noncomputable section

open scoped WeierstrassCurve.Affine TensorProduct
open Polynomial


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
