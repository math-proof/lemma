module

public import Mathlib
public import Abbrev.MvPolynomial_CrossingQuotient

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace MvPolynomial

variable (W : Type*) [CommRing W]

namespace CrossingQuotient

variable (t : W)

def monomial (n : ℤ) : CrossingQuotient W t :=
  if 0 ≤ n then mk t (X 0) ^ n.toNat else mk t (X 1) ^ (-n).toNat

def powMap (e : ℕ) : CrossingQuotient W (t ^ e) →ₐ[W] CrossingQuotient W t :=
  Ideal.Quotient.liftₐ (Ideal.span {(X 0 * X 1 - C (t ^ e) : MvPolynomial (Fin 2) W)})
    (aeval fun i : Fin 2 => mk t (X i) ^ e) (by
      intro p hp
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hp
      rw [map_mul, map_sub, map_mul, aeval_X, aeval_X, aeval_C, ← mul_pow, mk_X_mul_mk_X, ← map_pow, sub_self,
        mul_zero])

end CrossingQuotient

end MvPolynomial

end

end
