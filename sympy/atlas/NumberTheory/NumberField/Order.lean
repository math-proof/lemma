/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Order.lean -/

import Mathlib.NumberTheory.NumberField.Basic

/-! An order in a number field `K` is a `ℤ`-subalgebra of `K` contained in the
integral closure `integralClosure ℤ K = 𝓞 K` whose fraction field is `K`.
This formalizes arXiv:2608.02983v1, TypesofQuartic25.tex line 136:
> Let K be an algebraic number field and O_K its ring of integers, and O an order
> in O_K (a subring of O_K with quotient field K). -/
def NumberField.IsOrder (K : Type*) [Field K] [NumberField K] (O : Subalgebra ℤ K) : Prop :=
  O ≤ integralClosure ℤ K ∧ IsFractionRing O K

namespace NumberField.IsOrder

variable {K : Type*} [Field K] [NumberField K] {O : Subalgebra ℤ K}

/-- Elimination for the integral-closure inclusion clause. -/
theorem le_integralClosure (h : NumberField.IsOrder K O) :
    O ≤ integralClosure ℤ K :=
  h.1

/-- Elimination for the fraction-ring clause. Does not install a global instance. -/
theorem isFractionRing (h : NumberField.IsOrder K O) :
    IsFractionRing O K :=
  h.2

/-- Every element of `K` is a quotient of elements of the order. Uses the local
`IsFractionRing O K` evidence and `IsFractionRing.div_surjective`. -/
theorem exists_div_eq (hO : NumberField.IsOrder K O) (x : K) :
    ∃ (a b : O), b ≠ 0 ∧ (a : K) / (b : K) = x := by
  let _inst : IsFractionRing O K := hO.isFractionRing
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := O) x
  exact ⟨a, b, mem_nonZeroDivisors_iff_ne_zero.mp hb, by simpa using hab⟩

end NumberField.IsOrder

/-- The maximal order `integralClosure ℤ K = 𝓞 K` is an order. -/
theorem NumberField.isOrder_integralClosure (K : Type*) [Field K] [NumberField K] :
    NumberField.IsOrder K (integralClosure ℤ K) := by
  constructor
  · exact le_rfl
  · exact integralClosure.isFractionRing_of_finite_extension ℚ _
