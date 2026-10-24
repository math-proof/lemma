/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/ArtinGroup.lean -/

import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.Coxeter.Matrix

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

/-- The alternating product `a * b * a * b * ⋯` of length `n` in a monoid, starting with `a`. -/
def alternatingWord {G : Type*} [Monoid G] (a b : G) : ℕ → G
  | 0 => 1
  | n + 1 => a * alternatingWord b a n

/-- The Artin (braid) relation for the ordered pair `(i, j)`: the two alternating words of length
`M i j` in the generators `i` and `j` agree. It is encoded in the free group as
`⟨s i · s j · ⋯⟩ · ⟨s j · s i · ⋯⟩⁻¹`, which lies in the relation set exactly when both words are
declared equal. -/
def artinRelation (i j : B) : FreeGroup B :=
  alternatingWord (FreeGroup.of i) (FreeGroup.of j) (M i j) *
    (alternatingWord (FreeGroup.of j) (FreeGroup.of i) (M i j))⁻¹

/-- The set of Artin relations of `M`: one braid relation for each ordered pair of distinct
generators whose off-diagonal entry is finite (`M i j ≠ 0`, i.e. `m i j ≠ ∞`). Pairs with
`M i j = ∞` contribute no relation. -/
def artinRelationsSet : Set (FreeGroup B) :=
  { r | ∃ i j, i ≠ j ∧ M i j ≠ 0 ∧ r = M.artinRelation i j }

/-- The **Artin group** (Artin–Tits group) of a Coxeter matrix `M`: the group presented by the
generators `s i` (`i : B`) subject only to the braid relations of `artinRelationsSet M`. Unlike the
Coxeter group `M.Group`, no involution relations `s i ^ 2 = 1` are imposed. -/
def ArtinGroup := PresentedGroup M.artinRelationsSet

instance : Group M.ArtinGroup := inferInstanceAs (Group (PresentedGroup _))

namespace ArtinGroup

/-- The generator `s i` of the Artin group of `M`. -/
def of (i : B) : M.ArtinGroup := PresentedGroup.of i
end ArtinGroup
end CoxeterMatrix
