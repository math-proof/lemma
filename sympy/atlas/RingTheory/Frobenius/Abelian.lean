/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Frobenius/Abelian.lean -/

import Mathlib.RingTheory.Frobenius

/-!
# Arithmetic Frobenius is independent of the prime above in abelian extensions

ATLAS source: [`v1/Atlas/NumberTheoryI/code/RayClassFields.lean`, lines 714--729](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/RayClassFields.lean#L714-L729)
(`arithFrobAt_eq_of_under_eq`), frozen at commit
`e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`.

Source-to-API mapping: frozen ATLAS `RayClassFields.lean` lines 714--729, source
declaration `arithFrobAt_eq_of_under_eq`, maps to this module's root declaration
`arithFrobAt_eq_of_under_eq`.

This module is N402 C2a only: the arithmetic Frobenius elements at two primes
lying over the same base prime are equal when the acting group is commutative.
The source proves this by obtaining Mathlib's conjugacy theorem
(`isConj_arithFrobAt`) and collapsing the conjugacy by commutativity
(membership in the center). Chosen-prime constructions, restriction-equality
results, Artin maps, and the final compatibility stages are excluded.

Generalized from the source's number-field Galois group
(`L ≃ₐ[K] L` with `KroneckerWeber.IsAbelianExtension K L`) to Mathlib's natural
Frobenius setting (`Group G` with `IsMulCommutative G`). No unramifiedness
hypothesis is required.

This declaration lives in the root namespace, matching `arithFrobAt` and
`isConj_arithFrobAt`.
-/

variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
  [Finite G] [Algebra.IsInvariant R S G]
