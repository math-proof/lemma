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

end Int
