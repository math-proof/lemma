/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/IntermediateField.lean -/

import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.Order.ModularLattice
import Mathlib.RingTheory.ZMod.UnitsCyclic
import sympy.atlas.FieldTheory.Galois.Abelian
import Lemma.Rat.Galois.Abelian
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

open scoped IntermediateField IsMulCommutative

private theorem uniqueSubgroupOfIndex (G : Type*) [Group G] [Finite G] [IsCyclic G]
    (s : ℕ) (hs : s ∣ Nat.card G) :
    ∃! H : Subgroup G, H.index = s := by
  let H : Subgroup G := (powMonoidHom s : G →* G).range
  have hH : H.index = s := by
    rw [IsCyclic.index_powMonoidHom_range, Nat.gcd_eq_right_iff_dvd.mpr hs]
  refine ⟨H, hH, ?_⟩
  intro J hJ
  symm
  apply Subgroup.eq_of_le_of_card_ge (H := H) (K := J)
  · intro x hx
    change x ∈ (powMonoidHom s : G →* G).range at hx
    rcases hx with ⟨y, rfl⟩
    rw [powMonoidHom_apply, ← hJ]
    exact J.pow_index_mem y
  · have hHcard := H.index_mul_card
    have hJcard := J.index_mul_card
    rw [hH] at hHcard
    rw [hJ] at hJcard
    have hspos : 0 < s := Nat.pos_of_dvd_of_pos hs Nat.card_pos
    exact Nat.le_of_mul_le_mul_left (by simp [hHcard, hJcard]) hspos

namespace CyclotomicField

/-- For prime `p` and `s ∣ p - 1`, there is a unique intermediate field of
`CyclotomicField p ℚ` whose degree over `ℚ` is `s`. -/
theorem existsUnique_intermediateField_finrank (p s : ℕ) (hp : p.Prime)
    (hs : s ∣ p - 1) :
    ∃! K : IntermediateField ℚ (CyclotomicField p ℚ), Module.finrank ℚ K = s := by
  let _ : NeZero p := ⟨hp.ne_zero⟩
  let _ : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    instIsCyclotomicExtensionSingletonNatSetOfCharZero p ℚ
  let _ : IsGalois ℚ (CyclotomicField p ℚ) :=
    IsCyclotomicExtension.isGalois {p} ℚ (CyclotomicField p ℚ)
  let _ : IsCyclic Gal(CyclotomicField p ℚ / ℚ) := by
    have hz : IsCyclic ((ZMod p)ˣ) := ZMod.isCyclic_units_prime hp
    exact isCyclic_of_surjective
      (IsCyclotomicExtension.Rat.galEquivZMod p (CyclotomicField p ℚ)).symm.toMonoidHom
      (IsCyclotomicExtension.Rat.galEquivZMod p (CyclotomicField p ℚ)).symm.surjective
  have hcard : Nat.card Gal(CyclotomicField p ℚ / ℚ) = p - 1 := by
    rw [IsGalois.card_aut_eq_finrank, IsCyclotomicExtension.Rat.finrank (k := p),
      Nat.totient_prime hp]
  have hs' : s ∣ Nat.card Gal(CyclotomicField p ℚ / ℚ) := hcard ▸ hs
  obtain ⟨H, hH, hunique⟩ :=
    uniqueSubgroupOfIndex Gal(CyclotomicField p ℚ / ℚ) s hs'
  refine ⟨IntermediateField.fixedField H, ?_, ?_⟩
  · change Module.finrank ℚ (IntermediateField.fixedField H) = s
    rw [IntermediateField.finrank_eq_fixingSubgroup_index,
      IntermediateField.fixingSubgroup_fixedField, hH]
  · intro K hK
    have hKindex : K.fixingSubgroup.index = s := by
      rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
      exact hK
    have hfix : K.fixingSubgroup = H := hunique K.fixingSubgroup hKindex
    rw [← IsGalois.fixedField_fixingSubgroup K, hfix]

/-- The unique degree-`s` intermediate field of the `p`-th cyclotomic field. -/
noncomputable def intermediateFieldOfFinrank (p s : ℕ) (hp : p.Prime) (hs : s ∣ p - 1) :
    IntermediateField ℚ (CyclotomicField p ℚ) :=
  (existsUnique_intermediateField_finrank p s hp hs).choose
end CyclotomicField
