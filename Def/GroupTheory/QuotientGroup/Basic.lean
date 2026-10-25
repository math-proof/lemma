/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/QuotientGroup/Basic.lean -/

import Mathlib.GroupTheory.QuotientGroup.Basic
/-!
# Quotients by subgroups containing a homomorphism kernel

This module provides the canonical isomorphism between the quotient of a
commutative group by a subgroup containing a homomorphism kernel and the
corresponding quotient of the homomorphism range.

## Main results

* `QuotientGroup.quotientEquivRangeQuotient`: for `f : A →* C` and
  `B : Subgroup A` with `f.ker ≤ B`, the canonical isomorphism
  `A ⧸ B ≃* f.range ⧸ (B.map f).subgroupOf f.range`.
* `QuotientGroup.quotientEquivRangeQuotient_mk`: evaluation on representatives.
-/


namespace QuotientGroup

/-- Canonical isomorphism `A ⧸ B ≃* f.range ⧸ (B.map f).subgroupOf f.range`
for a homomorphism `f : A →* C` of commutative groups and a subgroup
`B : Subgroup A` containing `f.ker`. -/
@[to_additive
/-- Canonical isomorphism `A ⧸ B ≃+ f.range ⧸ (B.map f).addSubgroupOf f.range`
for a homomorphism `f : A →+ C` of additive commutative groups and an
additive subgroup `B : AddSubgroup A` containing `f.ker`. -/]
noncomputable def quotientEquivRangeQuotient
    {A C : Type*} [CommGroup A] [CommGroup C]
    (f : A →* C) (B : Subgroup A) (hB : f.ker ≤ B) :
    A ⧸ B ≃* f.range ⧸ (B.map f).subgroupOf f.range := by
  let φ : A →* f.range ⧸ (B.map f).subgroupOf f.range :=
    (QuotientGroup.mk' _).comp f.rangeRestrict
  have hφ : Function.Surjective φ := by
    intro q
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective _ q
    obtain ⟨x, rfl⟩ := f.rangeRestrict_surjective z
    exact ⟨x, rfl⟩
  have hcomp : ∀ x : A, φ x = QuotientGroup.mk (f.rangeRestrict x) :=
    fun x => rfl
  have hker : B = φ.ker := by
    ext x
    simp only [MonoidHom.mem_ker, hcomp, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    · intro hx
      obtain ⟨b, hb, hfb⟩ := Subgroup.mem_map.mp hx
      have hfbx : f b = f x := hfb
      have h1 : f (b⁻¹ * x) = 1 := by
        rw [map_mul, map_inv, hfbx, inv_mul_cancel]
      have h2 : b⁻¹ * x ∈ B := hB (MonoidHom.mem_ker.mpr h1)
      have hxeq : x = b * (b⁻¹ * x) := (mul_inv_cancel_left b x).symm
      rw [hxeq]
      exact B.mul_mem hb h2
  exact (QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)

end QuotientGroup
