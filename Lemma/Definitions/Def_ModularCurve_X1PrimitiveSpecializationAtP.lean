import Mathlib
import Lemma.Definitions.Def_FLTPrelim_Ramification
import Lemma.Definitions.Def_EllipticCurve_FrobeniusTrace
import Lemma.Definitions.Def_EllipticCurve_TateModule
import Lemma.Definitions.Def_ModularCurve_X1HeckeModule
import Lemma.Definitions.Def_ModularCurve_X1PrimitiveSpecialization
import Lemma.Definitions.Def_ModularCurve_QExpFrobeniusModL

set_option autoImplicit false

noncomputable section

open IntermediateField AlgebraicCurve CongruenceSubgroup

namespace ModularCurve

section NormFree

variable (M p : ℕ)

def normFreeRepsAt : Finset ℕ :=
  (Finset.range M).filter (fun d => Nat.Coprime d M ∧ d ≡ 1 [MOD M / p])

variable {M p} in
theorem mem_normFreeRepsAt {d : ℕ} :
    d ∈ normFreeRepsAt M p ↔ d < M ∧ Nat.Coprime d M ∧ d ≡ 1 [MOD M / p] := by
  rw [normFreeRepsAt, Finset.mem_filter, Finset.mem_range]

def normFreePartAt : AddSubgroup (JOne M) :=
  (normFreeEnd M (normFreeRepsAt M p)).range

variable {M p} in
theorem mem_normFreePartAt {y : JOne M} :
    y ∈ normFreePartAt M p ↔ ∃ x, normFreeEnd M (normFreeRepsAt M p) x = y :=
  AddMonoidHom.mem_range

theorem normFreeEnd_mem_normFreePartAt (x : JOne M) :
    normFreeEnd M (normFreeRepsAt M p) x ∈ normFreePartAt M p :=
  ⟨x, rfl⟩

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
