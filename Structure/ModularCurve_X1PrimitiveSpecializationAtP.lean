module

public import Mathlib
public import Def.FLTPrelim_Ramification
public import Instance.EllipticCurve_FrobeniusTrace
public import Instance.EllipticCurve_TateModule
public import Def.ModularCurve_X1HeckeModule
public import Theorem.MvPolynomial.X1HeckeModule
public import Structure.ModularCurve_X1PrimitiveSpecialization
public import Def.ModularCurve_QExpFrobeniusModL
public import Theorem.LaurentSeries.QExpFrobeniusModL
public import Def.ModularCurve_X1PrimitiveSpecializationAtP

set_option autoImplicit false

public noncomputable section

open IntermediateField AlgebraicCurve CongruenceSubgroup

namespace ModularCurve

section NormFree

variable (M p : ℕ)


variable {M p} in


variable {M p} in


end NormFree

section Datum

variable (M p : ℕ) [Fact p.Prime] (P : ValuationSubring (AlgebraicClosure ℚ))
variable (k : Type) [Field k] [CharP k p]

structure X1PrimitiveSpecializationAtP where

  spInf : normFreePartAt M p →+ Pic0 k (qExpFunctionFieldC k (Gamma1 M))

  spZero : normFreePartAt M p →+ Pic0 k (qExpFunctionFieldC k (Gamma1 M))

  spInf_smul_of_mem_inertia : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ (y : normFreePartAt M p)
    (h : σ • (y : JOne M) ∈ normFreePartAt M p), spInf ⟨_, h⟩ = spInf y

  spZero_smul_eq_zero : ∀ σ ∈ P.decompositionSubgroup ℚ, ∀ (y : normFreePartAt M p)
    (h : σ • (y : JOne M) ∈ normFreePartAt M p), spZero y = 0 → spZero ⟨_, h⟩ = 0

  spInf_smul_of_isFrobeniusAt : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
    P.IsFrobeniusAt σ p → ∀ (y : normFreePartAt M p) (h : σ • (y : JOne M) ∈ normFreePartAt M p),
      spInf ⟨_, h⟩ = qExpFrobeniusPushforwardModL k (Gamma1 M) p (spInf y)

  spInf_hecke_of_spZero_eq_zero : ∀ (y : normFreePartAt M p)
    (h : heckeOperatorOneBar M ⟨p, Fact.out⟩ (y : JOne M) ∈ normFreePartAt M p),
    spZero y = 0 → spInf ⟨_, h⟩ = qExpFrobeniusPullbackModL k (Gamma1 M) p (spInf y)

  spZero_hecke_eq_zero : ∀ (y : normFreePartAt M p)
    (h : heckeOperatorOneBar M ⟨p, Fact.out⟩ (y : JOne M) ∈ normFreePartAt M p),
    spZero y = 0 → spZero ⟨_, h⟩ = 0

  exists_spZero_hecke_eq : ∀ (x : TateModule p (JOne M))
    (hx : ∀ n, (x : ℕ → JOne M) n ∈ normFreePartAt M p),
    ∃ x' : TateModule p (JOne M), (∀ n, (x' : ℕ → JOne M) n ∈ normFreePartAt M p) ∧
      ∀ (n : ℕ) (h : heckeOperatorOneBar M ⟨p, Fact.out⟩ ((x' : ℕ → JOne M) n) ∈ normFreePartAt M p),
        spZero ⟨_, h⟩ = spZero ⟨_, hx n⟩

  exists_smul_mem_span_of_forall_eq_zero : ∀ (x : TateModule p (JOne M))
    (hx : ∀ n, (x : ℕ → JOne M) n ∈ normFreePartAt M p),
    (∀ n, spInf ⟨_, hx n⟩ = 0) → (∀ n, spZero ⟨_, hx n⟩ = 0) →
      ∃ m : ℕ, m ≠ 0 ∧ ((m : ℤ_[p]) • x) ∈ Submodule.span ℤ_[p]
        {z : TateModule p (JOne M) |
          ∃ τ ∈ P.inertiaSubgroupIn ℚ, (∀ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 → τ ζ = ζ) ∧
            ∃ y : TateModule p (JOne M), (∀ n, (y : ℕ → JOne M) n ∈ normFreePartAt M p) ∧
              z = TateModule.rep p (JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) τ y - y}

end Datum

end ModularCurve

end
