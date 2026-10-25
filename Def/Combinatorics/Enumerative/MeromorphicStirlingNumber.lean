/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeromorphicStirlingNumber.lean -/

import Mathlib.Data.Nat.Choose.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
/-!
# Meromorphic Stirling and Bessel numbers

This file formalizes the two explicit identifications in Schork,
*On Generalized Stirling Numbers and Normal Ordering*:
<https://cs.uwaterloo.ca/journals/JIS/VOL15/Schork/schork2.tex>.
-/


namespace MetaMathlibExt

/-- Meromorphic Stirling member `S_{2;-1}` from its StirW1 formula.

Concept `meromorphic Stirling number` (`jis_sem_0210f8899dc06a2d15855412`),
source `jis_source_f3006b7ef496c012bfca9644`, statement `jis_9901739ac9112adc8aea1afb`,
required clause `first_meromorphic`: `(-1)^(n-k)*(n-1)!/(2^(n-k)*(k-1)!)*choose(2n-k-1,n-1)`
on `1 <= k <= n`. Defined independently from the Bessel side. -/
def meromorphicStirlingFirst (n k : ℕ) : ℚ :=
  (((-1 : ℚ) ^ (n - k) * (((n - 1).factorial : ℕ) : ℚ)) /
    (((2 : ℚ) ^ (n - k)) * ((((k - 1).factorial : ℕ)) : ℚ))) *
    (((Nat.choose (2 * n - k - 1) (n - 1) : ℕ)) : ℚ)

/-- Meromorphic Stirling member `S_{-1;1}` from its StirW2 formula.

Concept `meromorphic Stirling number` (`jis_sem_0210f8899dc06a2d15855412`),
source `jis_source_f3006b7ef496c012bfca9644`, statement `jis_9901739ac9112adc8aea1afb`,
required clause `second_meromorphic`: `(2n-2k)!/(2^(n-k)*(n-k)!)*choose(n,2k-n)`
on `n <= 2*k` and `k <= n`. Defined independently from the Bessel side. -/
def meromorphicStirlingSecond (n k : ℕ) : ℚ :=
  ((((2 * n - 2 * k).factorial : ℕ)) : ℚ) /
    (((2 : ℚ) ^ (n - k)) * ((((n - k).factorial : ℕ)) : ℚ)) *
    (((Nat.choose n (2 * k - n) : ℕ)) : ℚ)

/-- Bessel number of the first kind `b` from its Bessfirst formula.

Concept `meromorphic Stirling number` (`jis_sem_0210f8899dc06a2d15855412`),
source `jis_source_f3006b7ef496c012bfca9644`, statement `jis_9901739ac9112adc8aea1afb`,
required clause `first_bessel`: `(-1)^(n-k)*(2n-k-1)!/(2^(n-k)*(k-1)!*(n-k)!)`
on `1 <= k <= n`. Defined independently from the meromorphic side. -/
def besselNumberFirst (n k : ℕ) : ℚ :=
  ((-1 : ℚ) ^ (n - k) * ((((2 * n - k - 1).factorial : ℕ)) : ℚ)) /
    (((2 : ℚ) ^ (n - k)) * ((((k - 1).factorial : ℕ)) : ℚ) *
      ((((n - k).factorial : ℕ)) : ℚ))

/-- Bessel number of the second kind `B` from its Besssecond formula.

Concept `meromorphic Stirling number` (`jis_sem_0210f8899dc06a2d15855412`),
source `jis_source_f3006b7ef496c012bfca9644`, statement `jis_9901739ac9112adc8aea1afb`,
required clause `second_bessel`: `n!/(2^(n-k)*(2k-n)!*(n-k)!)`
on `n <= 2*k` and `k <= n`. Defined independently from the meromorphic side. -/
def besselNumberSecond (n k : ℕ) : ℚ :=
  ((((n.factorial : ℕ))) : ℚ) /
    (((2 : ℚ) ^ (n - k)) * ((((2 * k - n).factorial : ℕ)) : ℚ) *
      ((((n - k).factorial : ℕ)) : ℚ))

end MetaMathlibExt
