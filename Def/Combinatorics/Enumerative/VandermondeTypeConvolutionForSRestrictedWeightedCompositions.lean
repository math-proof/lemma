/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/VandermondeTypeConvolutionForSRestrictedWeightedCompositions.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fin.Basic
open scoped BigOperators

/-!
# Vandermonde-type convolution for S-restricted weighted compositions

Source: Steffen Eger, *Restricted Weighted Integer Compositions and Extended
Binomial Coefficients*, Journal of Integer Sequences 16 (2013), Article 13.5.4:
<https://cs.uwaterloo.ca/journals/JIS/VOL16/Eger/eger6.tex>.
Primary-source SHA-256:
`5c71bf597c6a2a87343e5612aa3c1dc7d435c66305d871a41850c27803971b3b`.
Definition `d_{S,f}` (lines 278–290); Vandermonde lemma and coefficient proof
(lines 431–505); direct combinatorial split at the first `j` parts
(lines 1433–1456).

Canonical source identifiers: concept `jis_sem_2ade353e04d8b61cffa56696`,
statement `jis_b88b976b121b187052834c84`.

The statement generalizes the paper's weight function from `S → R` to `ℕ → R`;
only values on `S` occur, so this is faithful.
-/


namespace MathlibExt.Combinatorics.Enumerative

/-- Weighted count of `S`-restricted `f`-weighted compositions of `n` with `k` parts.

For a commutative ring `R`, a finite set `S` of nonnegative integers, and a weight
function `f : ℕ → R`, this is the sum over all tuples with every part in `S` and
total `n` of the product weight `∏ i, f (π i)`. Since every part of a composition
of `n` is at most `n`, tuples are encoded over the finite type `Fin k → Fin (n + 1)`
with parts coerced to `ℕ`. -/
noncomputable def sRestrictedWeightedCompositionCount {R : Type*} [CommRing R]
    (S : Finset ℕ) (f : ℕ → R) (n k : ℕ) : R := by
  classical
  exact ∑ π ∈ Finset.univ.filter
    (fun π : Fin k → Fin (n + 1) => (∀ i, (π i : ℕ) ∈ S) ∧ ∑ i, (π i : ℕ) = n),
      ∏ i, f (π i)

end MathlibExt.Combinatorics.Enumerative
