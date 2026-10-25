/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/FiniteCongruence.lean -/

import Theorem.NumberTheory.NumberField.RayClass.RayGroup.Part3
import Lemma.Nat.NumberField.RayClass.RayGroup
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.FractionalIdeal.Operations
import Theorem.NumberTheory.NumberField.RayClass.FiniteCongruence.Part3
@[expose] noncomputable section

open scoped nonZeroDivisors

/-!
# Finite congruence, the finite ray-one subgroup, and admissible representatives (N406)

Source mapping (documentation only; no statement/proof changes):
* ATLAS source: [`v1/Atlas/NumberTheoryI/code/RayClassFields.lean`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/RayClassFields.lean#L1206-L2011),
  NumberTheoryI N406, Theorem 21.8, Section 21.3; the final declaration is
  [`RayClassField.theorem_21_8_quotient_iso`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/RayClassFields.lean#L2607-L2647).
* Full source target: the ray-class exact sequence and canonical isomorphism
  `K^m / K^{m,1} ≃ {±1}^{#m∞} × (O_K / m₀)ˣ`. This file is only a finite-kernel
  prerequisite toward that target, not the full theorem.

Helper for ray-class congruence arguments: if `x + y ≠ 0` and both principal
fractional ideals `(x)`, `(y)` have `v`-adic count at least `n`, then so does
`(x + y)`. The nonzero cases go through the `v`-adic valuation and its
nonarchimedean inequality; the zero-summand cases are handled separately.

Main results:
* `rayElement_count_spanSingleton_eq_zero`: a member of `rayElements m` has
  principal fractional-ideal count zero at every finite prime supported by `m`.
* `rayElement_valuation_eq_one`: a ray element has valuation one at every finite
  prime supported by `m`.
* `mem_rayElements_of_valuation_eq_one`: converse valuation-one criterion —
  valuation one at every finite prime supported by `m` gives a ray element.
* `CongruentOneAtFinitePart.mul` / `.inv`: closure of the finite-part
  congruence under multiplication and inversion for ray elements.
* `finiteRayOneElements`: the subgroup of `rayElements m` cut out by the
  finite-part congruence.
* `exists_isUnit_mod_finitePart_div_eq`: every ray element is a quotient of
  two integers both coprime to the finite part of the modulus.
* `quotientUnits_div_eq_of_div_eq`: equal fraction values give equal
  finite-quotient units.
* `finiteResidueMap`: the finite-part residue homomorphism on ray elements.
* `finiteResidueMap_apply_of_div_eq`: computation API for `finiteResidueMap`
  from any admissible representative pair.
* `finiteResidueMap_eq_one_iff`: kernel of `finiteResidueMap` is the
  finite-part congruence.
* `finiteResidueMap_ker`: the kernel of `finiteResidueMap` equals
  `finiteRayOneElements`.
* `finiteResidueMap_eq_one_of_valuation_le`: valuation criterion for triviality
  of `finiteResidueMap` at every supported finite place.

Cumulative finite-kernel source map toward `RayClassField.theorem_21_8_quotient_iso`:
* PR #1035, `count_spanSingleton_add_ge_of_ne_zero`: principal-ideal-count
  counterpart of the finite-congruence multiplication step in
  `RayClassField.UnitsCongruent_subgroup'`; the source rewrites
  `ab - 1 = a * (b - 1) + (a - 1)` and applies `Valuation.map_add`, while the
  helper isolates preservation of a shared count bound under addition.
* PR #1039, `CongruentOneAtFinitePart.mul`, `.inv`, `finiteRayOneElements`:
  `rayElements m` corresponds to ambient `UnitsCoprime_subgroup' K 𝔪`, while
  `finiteRayOneElements m` packages exactly the finite congruence component of
  `UnitsCongruent_subgroup' K 𝔪`; the `mul`/`inv` proofs correspond to its
  finite-place `mul_mem'`/`inv_mem'` clauses, its separate infinite-place
  positivity clause lying outside this finite subgroup.
* PR #1043, `rayElement_valuation_eq_one`, `exists_isUnit_mod_finitePart_div_eq`:
  the former realizes the supported-place normalized-valuation-one property in
  ambient `UnitsCoprime_subgroup' K 𝔪` (compare
  `valuation_eq_one_of_spanSingleton_coprime'`); the latter is the native-API
  counterpart of `coprime_rep_exists`, writing a ray element as `a / b` with
  both integral images units modulo the finite part.
* PR #1046, `finiteResidueMap`, `finiteResidueMap_apply_of_div_eq`: native-API
  counterpart of `finitePartMapHom`; the computation theorem and its private
  implementation encode `coprime_rep_well_def`, namely independence of the
  admissible `a / b` and the value `a * b⁻¹` in quotient units.
* PR #1052, `finiteResidueMap_eq_one_iff`, `finiteResidueMap_ker`: native-API
  counterpart of `finitePartMapHom_ker_iff` and its subgroup-kernel packaging,
  identifying the kernel with `finiteRayOneElements` for the kernel computation
  used by `RayClassField.theorem_21_8_quotient_iso`.
* PR #1093, `mem_rayElements_of_valuation_eq_one`: converse bridge from
  normalized valuation one at every supported finite place to `rayElements m`
  membership; corresponds to the membership condition built into
  `UnitsCoprime_subgroup' K 𝔪`, used in `weak_approx_coprime_sign_finitePart`
  when its controlled approximation witness is packaged as an ambient coprime
  unit.
* PR #1107, `finiteResidueMap_eq_one_of_valuation_le`: the direct
  valuation-bound criterion for trivial finite residue, packaging the
  finite-place congruence implication used in the kernel calculation.
-/


namespace NumberField

namespace Modulus

variable {K : Type*} [Field K] [NumberField K]

/-- Finite-part residue homomorphism on ray elements.
Source (N406 §21.3): the
[`finitePartMapHom`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/RayClassFields.lean#L1812-L1864)
finite component of the quotient isomorphism. -/
noncomputable def finiteResidueMap (m : Modulus K) :
    rayElements m →* (𝓞 K ⧸ (m.finitePart : Ideal (𝓞 K)))ˣ where
  toFun := finiteResidueMapFn m
  map_one' := by
    have h := finiteResidueMapFn_eq_of_div_eq m 1 1 1 isUnit_one isUnit_one
      (by simp)
    simpa using h
  map_mul' := fun x y => by
    obtain ⟨a1, b1, ha1, hb1, r1⟩ := exists_isUnit_mod_finitePart_div_eq m x
    obtain ⟨a2, b2, ha2, hb2, r2⟩ := exists_isUnit_mod_finitePart_div_eq m y
    have h12a : IsUnit
        (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) (a1 * a2)) := by
      rw [map_mul]
      exact IsUnit.mul ha1 ha2
    have h12b : IsUnit
        (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) (b1 * b2)) := by
      rw [map_mul]
      exact IsUnit.mul hb1 hb2
    have hfrac : algebraMap (𝓞 K) K (a1 * a2) / algebraMap (𝓞 K) K (b1 * b2) =
        (((x * y : rayElements m) : Kˣ) : K) := by
      rw [map_mul, map_mul, ← div_mul_div_comm, r1, r2, Subgroup.coe_mul,
        Units.val_mul]
    have hx := finiteResidueMapFn_eq_of_div_eq m x a1 b1 ha1 hb1 r1
    have hy := finiteResidueMapFn_eq_of_div_eq m y a2 b2 ha2 hb2 r2
    have hxy := finiteResidueMapFn_eq_of_div_eq m (x * y) (a1 * a2) (b1 * b2)
      h12a h12b hfrac
    have hu1 : h12a.unit = ha1.unit * ha2.unit := by
      apply Units.ext
      simp only [Units.val_mul, IsUnit.unit_spec, map_mul]
    have hu2 : h12b.unit = hb1.unit * hb2.unit := by
      apply Units.ext
      simp only [Units.val_mul, IsUnit.unit_spec, map_mul]
    change finiteResidueMapFn m (x * y) =
      finiteResidueMapFn m x * finiteResidueMapFn m y
    rw [hx, hy, hxy, hu1, hu2]
    simp [mul_inv_rev, mul_comm, mul_assoc, mul_left_comm]

end Modulus
end NumberField
