/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/IntermediateField.lean -/

import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.Order.ModularLattice
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Theorem.FieldTheory.Galois.Abelian
import Lemma.Rat.Galois.Abelian
import Theorem.NumberTheory.Cyclotomic.IntermediateField
open scoped IntermediateField IsMulCommutative

/-!
# Intermediate fields of prime cyclotomic fields

For every divisor `s` of `p - 1`, the `p`-th cyclotomic field over `ℚ` has a unique intermediate
field of degree `s`.

## LCM conductors generate the ambient field

`CyclotomicField.sup_eq_top_of_lcm_eq` says that two cyclotomic intermediate fields of
`CyclotomicField m ℚ`, of conductors `n₀` and `n₁` with `Nat.lcm n₀ n₁ = m`,
generate the whole field. `CyclotomicField.inf_ne_bot_of_lt_of_lcm_eq` is the immediate
modular-lattice consequence: any field strictly above the first factor meets the second
factor nontrivially.

Source-to-API map from `Atlas/NumberTheoryI/code/AnalyticClassNumber.lean` at revision
`e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`, lines 1653--1708:

* `cyclotomic_coprime_sup_eq_top` maps to `CyclotomicField.sup_eq_top_of_lcm_eq`;
* `cyclotomic_coprime_nontrivial_ext` maps to `CyclotomicField.inf_ne_bot_of_lt_of_lcm_eq`.

The ATLAS source proves these for the `p`-free-part / `p`-power split of `m`; here the
hypothesis is the bare equality `Nat.lcm n₀ n₁ = m`, so no coprimality or `p`-adic
computation is needed. The modular-lattice argument installs
`IsAbelianGalois.isModularLattice_intermediateField` locally.

This closes only the lattice/intersection prerequisite: compositum unramifiedness and the
final N390 theorem are not addressed here.

## References

* T. P. da Nóbrega Neto, A. A. de Andrade, J. L. R. Bastos, R. R. de Araujo, and
  J. C. Interlando, *Algebraic Lattices Arising from Congruence Submodules in Subfields of p-th
  Cyclotomic Fields*, arXiv:2608.17056v1
-/


namespace CyclotomicField

/-- The unique degree-`s` intermediate field of the `p`-th cyclotomic field. -/
noncomputable def intermediateFieldOfFinrank (p s : ℕ) (hp : p.Prime) (hs : s ∣ p - 1) :
    IntermediateField ℚ (CyclotomicField p ℚ) :=
  (existsUnique_intermediateField_finrank p s hp hs).choose

end CyclotomicField
