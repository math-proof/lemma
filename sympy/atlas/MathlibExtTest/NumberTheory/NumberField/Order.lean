/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/Order.lean -/


import sympy.atlas.NumberTheory.NumberField.Order
import Lemma.Nat.NumberField.Order

-- Clause elimination
example {K : Type*} [Field K] [NumberField K] {O : Subalgebra ℤ K}
    (hO : NumberField.IsOrder K O) : O ≤ integralClosure ℤ K :=
  hO.le_integralClosure

example {K : Type*} [Field K] [NumberField K] {O : Subalgebra ℤ K}
    (hO : NumberField.IsOrder K O) : IsFractionRing O K :=
  hO.isFractionRing

-- Membership in an order implies integrality over ℤ
example {K : Type*} [Field K] [NumberField K] {O : Subalgebra ℤ K}
    (hO : NumberField.IsOrder K O) {x : K} (hx : x ∈ O) : IsIntegral ℤ x := by
  have hx' : x ∈ integralClosure ℤ K := hO.le_integralClosure hx
  exact hx'

-- Maximal-order boundary
example (K : Type*) [Field K] [NumberField K] :
    NumberField.IsOrder K (integralClosure ℤ K) :=
  NumberField.isOrder_integralClosure K

-- Concrete quotient witness for arbitrary x : K
example {K : Type*} [Field K] [NumberField K] {O : Subalgebra ℤ K}
    (hO : NumberField.IsOrder K O) (x : K) :
    ∃ (a b : O), b ≠ 0 ∧ (a : K) / (b : K) = x :=
  hO.exists_div_eq x

-- Same witness via div_surjective with local instance
example {K : Type*} [Field K] [NumberField K] {O : Subalgebra ℤ K}
    (hO : NumberField.IsOrder K O) (x : K) :
    ∃ (a b : O), b ≠ 0 ∧ (a : K) / (b : K) = x := by
  let _inst : IsFractionRing O K := hO.isFractionRing
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := O) x
  exact ⟨a, b, mem_nonZeroDivisors_iff_ne_zero.mp hb, by simpa using hab⟩
