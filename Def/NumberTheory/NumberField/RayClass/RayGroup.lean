/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/RayGroup.lean -/

import Theorem.NumberTheory.NumberField.RayClass.Modulus.Part5
import Lemma.Nat.NumberField.RayClass.Modulus
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.ClassGroup.Basic
@[expose] noncomputable section

open scoped nonZeroDivisors

/-!
# Ray groups attached to a modulus (N403 foundation)

Built over `NumberField.Modulus`, whose infinite-place multiplication
uses union, representing truncated exponent addition `min (m v + n v) 1`
(the ATLAS-extracted `max` formula was a typo).
-/


namespace NumberField

namespace Modulus

variable {K : Type*} [Field K] [NumberField K]

/-- Finite-prime support of a modulus: primes dividing the finite part. -/
def finiteSupported (m : Modulus K) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : Prop :=
  (m.finitePart : Ideal (𝓞 K)) ≤ v.asIdeal

/-- Exponent of the finite part of a modulus at a finite prime. -/
def finiteExponent (m : Modulus K) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : ℤ :=
  FractionalIdeal.count K v
    ((m.finitePart : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)

/-- Fractional ideals coprime to the finite part of a modulus. -/
def coprimeFractionalIdeals (m : Modulus K) :
    Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ where
  carrier :=
    { u |
      ∀ v, finiteSupported m v →
        FractionalIdeal.count K v (u : FractionalIdeal (𝓞 K)⁰ K) = 0 }
  one_mem' := by
    intro v _
    rw [Units.val_one]
    exact FractionalIdeal.count_one K v
  mul_mem' := by
    intro a b ha hb v hv
    rw [Units.val_mul]
    rw [FractionalIdeal.count_mul K v (Units.ne_zero a) (Units.ne_zero b)]
    rw [ha v hv, hb v hv, add_zero]
  inv_mem' := by
    intro a ha v hv
    rw [Units.val_inv_eq_inv_val]
    rw [FractionalIdeal.count_inv K v (a : FractionalIdeal (𝓞 K)⁰ K), ha v hv, neg_zero]

end Modulus
end NumberField
