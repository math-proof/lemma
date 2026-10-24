/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Ramsey.lean -/

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Fin

open scoped BigOperators

/-!
# Finite two-uniform Ramsey theorem

For `r ≥ 1` colors and every `k`, there is an `N` such that every coloring of
the 2-subsets of `Fin N` admits a monochromatic size-`k` set. This complements
`MathlibExt/Combinatorics/SimpleGraph/Ramsey.lean`, which covers the classical
graph (two-color, clique/independent-set) formulation; here the colors are
arbitrary (`Fin r`) and homogeneity is stated for set systems via
`Finset.powersetCard`.

Source: F. P. Ramsey, “On a Problem of Formal Logic,” Proceedings of the London
Mathematical Society s2-30 (1930), 264–286, DOI 10.1112/PLMS/S2-30.1.264.

Proof route: strong induction on the rank `∑ i, u i` of a target-size vector
`u : Fin r → ℕ`. If some target is `0`, `N = 0` works vacuously. Otherwise pick
a vertex `v`, pigeonhole the `N - 1` pairs through `v` into a large color fiber
`X`, pull the coloring back along the order embedding of a large finite subset
of `X`, apply the induction hypothesis to the decremented vector, and either
reattach `v` (same color) or keep the set found (different color).
-/

namespace MathlibExt.Combinatorics.Ramsey

private def RamseyProp (r : ℕ) (t : Fin r → ℕ) : Prop :=
  ∃ N : ℕ, ∀ φ : Finset (Fin N) → Fin r,
    ∃ i, ∃ S : Finset (Fin N), S.card = t i ∧ ∀ T ∈ S.powersetCard 2, φ T = i
end MathlibExt.Combinatorics.Ramsey
