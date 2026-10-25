import Mathlib
import Def.HeckeGalois_EichlerShimura

set_option autoImplicit false

noncomputable section

namespace ModularCurve

def eisensteinEval (N : ℕ) : HeckeAlg →ₐ[ℤ] ℤ :=
  MvPolynomial.aeval (eisensteinSystem N)


def eisensteinMaximalIdeal (N p : ℕ) : Ideal HeckeAlg :=
  Ideal.comap (eisensteinEval N) (Ideal.span {(p : ℤ)})


def IsEisensteinCongruent (m : ℕ) (N : ℕ) (a : Nat.Primes → ℤ) : Prop :=
  ∀ ℓ : Nat.Primes, (ℓ : ℕ) ≠ N → ((a ℓ : ZMod m)) = ((ℓ : ℕ) : ZMod m) + 1

def modSystem (m : ℕ) (a : Nat.Primes → ℤ) : Nat.Primes → ZMod m :=
  fun ℓ => (a ℓ : ZMod m)

end ModularCurve

end
