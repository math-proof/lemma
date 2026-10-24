import Mathlib
import Lemma.Definitions.Def_HeckeGalois_EichlerShimura

set_option autoImplicit false

noncomputable section

namespace ModularCurve

def eisensteinEval (N : ℕ) : HeckeAlg →ₐ[ℤ] ℤ :=
  MvPolynomial.aeval (eisensteinSystem N)

@[simp] lemma eisensteinEval_heckeGen (N : ℕ) (ℓ : Nat.Primes) :
    eisensteinEval N (heckeGen ℓ) = eisensteinSystem N ℓ := by
  simp [eisensteinEval, heckeGen]

def eisensteinMaximalIdeal (N p : ℕ) : Ideal HeckeAlg :=
  Ideal.comap (eisensteinEval N) (Ideal.span {(p : ℤ)})

lemma mem_eisensteinMaximalIdeal_iff (N p : ℕ) (t : HeckeAlg) :
    t ∈ eisensteinMaximalIdeal N p ↔ (p : ℤ) ∣ eisensteinEval N t := by
  rw [eisensteinMaximalIdeal, Ideal.mem_comap, Ideal.mem_span_singleton]

lemma natCast_mem_eisensteinMaximalIdeal (N p : ℕ) :
    (p : HeckeAlg) ∈ eisensteinMaximalIdeal N p := by
  rw [mem_eisensteinMaximalIdeal_iff, map_natCast]

def IsEisensteinCongruent (m : ℕ) (N : ℕ) (a : Nat.Primes → ℤ) : Prop :=
  ∀ ℓ : Nat.Primes, (ℓ : ℕ) ≠ N → ((a ℓ : ZMod m)) = ((ℓ : ℕ) : ZMod m) + 1

def modSystem (m : ℕ) (a : Nat.Primes → ℤ) : Nat.Primes → ZMod m :=
  fun ℓ => (a ℓ : ZMod m)

@[simp] lemma modSystem_apply (m : ℕ) (a : Nat.Primes → ℤ) (ℓ : Nat.Primes) :
    modSystem m a ℓ = (a ℓ : ZMod m) := rfl

end ModularCurve
