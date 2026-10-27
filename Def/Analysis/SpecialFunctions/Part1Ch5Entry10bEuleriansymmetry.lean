/-
Author: @akiezun, Avocado
-/

import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Range
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
/-!
# Ramanujan's Notebooks, Part I, Chapter 5

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace Ramanujan.Part1Ch5

namespace Entry10bEuleriansymmetry

open scoped BigOperators

open Finset

noncomputable section

/-- Even Euler (secant) numbers `E_{2n}`, defined by the binomial recurrence
`∑_{k = 0}^m (2m).choose (2k) * E_k = if m = 0 then 1 else 0`. -/
def chapter5EulerEven (n : ℕ) : ℤ :=
  Nat.strongRec (motive := fun _ => ℤ)
    (fun m previous =>
      if m = 0 then 1
      else -∑ k : Fin m,
        (Nat.choose (2 * m) (2 * k.val) : ℤ) * previous k.val k.isLt) n

end
end Entry10bEuleriansymmetry
end Ramanujan.Part1Ch5
end
