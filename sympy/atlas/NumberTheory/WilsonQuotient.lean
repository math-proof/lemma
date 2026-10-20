/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/WilsonQuotient.lean -/

import Mathlib.NumberTheory.Wilson

/-!
# Wilson quotient

This module defines the integer-valued Wilson quotient `W(p) = ((p-1)! + 1) / p`.

Primary source: Y. Matsuno, *A resolution of Kellner's conjectures on Wilson quotients*,
arXiv:2607.10106v1, lines 44–51, defines `W_p = ((p-1)! + 1) / p` for an odd prime `p`.
Downstream identity: M. Avitabile and S. Mattarei, *On some coefficients of the Artin-Hasse
series modulo a prime*, arXiv:2308.16034v1, `AH.tex` lines 315–321, uses
`(p-1)! = -1 + p * w_p`, i.e. `p * w_p = (p-1)! + 1`.

The definition is total as `ℕ → ℤ` via integer division; the source's odd-prime
domain is recorded as a hypothesis on the characterizing lemmas. Integrality
`p ∣ (p-1)! + 1` is Wilson's theorem, so the divisibility and exact-recovery
identities need only `p.Prime` (Wilson holds for `p = 2` as well); the oddness
restriction from the source is therefore not imposed on the theorems.
-/

namespace Int

/-- Wilson quotient `W(p) = ((p-1)! + 1) / p` as an integer.

For a prime `p` the quotient is integral by Wilson's theorem `p ∣ (p-1)! + 1`
(`ZMod.wilsons_lemma`). The definition is total on `ℕ`; the source domain
"odd prime" from Matsuno 2607.10106, ll. 44–51 is imposed as hypotheses where
needed in the lemmas, not in the type of the definition. -/
def wilsonQuotient (p : ℕ) : ℤ :=
  ((Nat.factorial (p - 1) : ℤ) + 1) / (p : ℤ)

/-- Exact recovery: `p * W(p) = (p-1)! + 1` for a prime `p`.

This is the `ℤ`-form of the identity `(p-1)! = -1 + p * w_p` used in
Avitabile–Mattarei 2308.16034, `AH.tex` ll. 315–321. By Wilson's theorem the
division in `wilsonQuotient` is exact, so multiplying back recovers the numerator. -/
theorem mul_wilsonQuotient (p : ℕ) (hp : Nat.Prime p) :
    (p : ℤ) * wilsonQuotient p = (Nat.factorial (p - 1) : ℤ) + 1 := by
  unfold wilsonQuotient
  have h_dvd : (p : ℤ) ∣ ((Nat.factorial (p - 1) : ℤ) + 1) := by
    let _ := Fact.mk hp
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    push_cast
    rw [ZMod.wilsons_lemma p]
    simp
  exact Int.mul_ediv_cancel' h_dvd

/-- Factorial form of the recovery identity: `(p-1)! = p * W(p) - 1`.

Equivalent to `mul_wilsonQuotient` with the `+1` moved, matching the
display `(p-1)! = -1 + p * w_p` from Avitabile–Mattarei `AH.tex` ll. 315–321. -/
theorem factorial_eq_mul_wilsonQuotient_sub_one (p : ℕ) (hp : Nat.Prime p) :
    (Nat.factorial (p - 1) : ℤ) = (p : ℤ) * wilsonQuotient p - 1 := by
  have h := mul_wilsonQuotient p hp
  omega

end Int
