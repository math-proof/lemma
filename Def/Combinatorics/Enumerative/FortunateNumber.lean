/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FortunateNumber.lean -/

import Mathlib.NumberTheory.Primorial
/-!
# Fortunate numbers

The definition is taken from Antonín Čejchan, Michal Křížek, and Lawrence
Somer, *On Remarkable Properties of Primes Near Factorials and Primorials*,
Journal of Integer Sequences 25 (2022), Article 22.1.4.
-/


namespace MetaMathlibExt

/-- `m` is the Fortunate number attached to the prime `q` when it is the
least integer greater than one for which `q# + m` is prime.

This reuses Mathlib's `primorial`. Stable source identifiers: concept
`jis_sem_a34930e523f9a76ac6ef3668`, statement
`jis_e3ac668676ad89d9b5e1b013`.
-/
def IsFortunateNumber (q m : ℕ) : Prop :=
  q.Prime ∧ 1 < m ∧ (primorial q + m).Prime ∧
    ∀ k, 1 < k → k < m → ¬ (primorial q + k).Prime

end MetaMathlibExt
