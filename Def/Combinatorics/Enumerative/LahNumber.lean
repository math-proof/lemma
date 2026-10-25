/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LahNumber.lean -/

import Mathlib.Data.Nat.Choose.Basic


namespace MetaMathlibExt

/-- The unsigned Lah number `L(n, k)`, which counts partitions of an `n`-element
set into `k` nonempty linearly ordered blocks. It is extended by zero outside
`1 ≤ k ≤ n`, with `L(0, 0) = 1`.

The closed formula is given in Maxie D. Schmidt, *Jacobi-Type Continued
Fractions for the Ordinary Generating Functions of Generalized Factorial
Functions*, Journal of Integer Sequences 20 (2017):
https://cs.uwaterloo.ca/journals/JIS/VOL20/Schmidt/schmidt14.tex. -/
def unsignedLahNumber : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 =>
    Nat.choose n k * Nat.factorial (n + 1) / Nat.factorial (k + 1)

/-- The signed Lah number `(-1) ^ (n - k) * L(n, k)` on `k ≤ n`, extended
by zero for `k > n`.

The sign convention is from Toufik Mansour, Matthias Schork, and Mark Shattuck,
*The Generalized Stirling and Bell Numbers Revisited*, Journal of Integer
Sequences 15 (2012):
https://cs.uwaterloo.ca/journals/JIS/VOL15/Schork/schork2.tex. -/
def signedLahNumber (n k : ℕ) : ℤ :=
  if k ≤ n then (-1 : ℤ) ^ (n - k) * unsignedLahNumber n k else 0

end MetaMathlibExt
