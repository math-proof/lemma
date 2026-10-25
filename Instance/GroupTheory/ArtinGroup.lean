/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/ArtinGroup.lean -/

import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.Coxeter.Matrix
import Def.GroupTheory.ArtinGroup
/-!
# Artin groups (Artin–Tits groups) of a Coxeter matrix

Given a Coxeter matrix `M` over an index type `B` (a symmetric matrix `M : Matrix B B ℕ` with
`M i i = 1` and `M i i' ≠ 1` for `i ≠ i'`, using the Mathlib convention `M i i' = 0 ↔ m i i' = ∞`),
its **Artin group** (or **Artin–Tits group**) is the group presented by generators `s i`, one for
each `i : B`, subject only to the braid relations

`s i * s j * s i * ⋯ = s j * s i * s j * ⋯`   (both words of length `M i j`),

one for each pair of distinct generators with a finite entry `M i j ≠ ∞`. The relation is omitted
when `M i j = ∞` (encoded as `M i j = 0`).

Adding the involution relations `s i ^ 2 = 1` to this presentation yields the Coxeter group
`M.Group`; equivalently, the quotient of the Artin group killing `s i ^ 2` recovers the Coxeter
group. (Merely deleting the involutions from the Coxeter presentation would leave power
relators `(s i * s j) ^ (M i j) = 1` instead of the braid equalities, a different group.) In
particular the braid group on `n + 1` strands is the Artin group of the type `Aₙ` Coxeter matrix.

## Main definitions

* `CoxeterMatrix.alternatingWord a b n`: the alternating product `a * b * a * ⋯` of length `n` in a
  monoid, starting with `a`.
* `CoxeterMatrix.artinRelation M i j`: the braid relation for the pair `(i, j)`, encoded as an
  element of the free group.
* `CoxeterMatrix.artinRelationsSet M`: the set of all braid relations of `M`.
* `CoxeterMatrix.ArtinGroup M`: the Artin group of `M`, presented on `B` by `artinRelationsSet M`.
* `CoxeterMatrix.ArtinGroup.of M i`: the generator `s i`.

## Main results

* `CoxeterMatrix.ArtinGroup.closure_range_of`: the generators generate the whole Artin group.
* `CoxeterMatrix.ArtinGroup.braid_relation`: the defining braid relation holds among the generators.

## References

* E. Brieskorn and K. Saito, *Artin-Gruppen und Coxeter-Gruppen*, Invent. Math. 17 (1972), 245-271.
* J. Tits, *Normalisateurs de tores I*, J. Algebra 4 (1966), 96-116.

## Tags

Artin group, Artin-Tits group, braid group, Coxeter matrix, presented group
-/


namespace CoxeterMatrix

variable {B : Type*}

instance : Group M.ArtinGroup := inferInstanceAs (Group (PresentedGroup _))

end CoxeterMatrix
