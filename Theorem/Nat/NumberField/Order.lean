module

public import Mathlib
public import Def.NumberTheory.NumberField.Order

public section


namespace NumberField.IsOrder

/--
[le_integralClosure](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Order.lean)
-/
public theorem le_integralClosure
  [Field K] [NumberField K]
  {O : Subalgebra ℤ K}
-- given
  (h : NumberField.IsOrder K O) :
-- imply
  O ≤ integralClosure ℤ K :=
-- proof
  h.1

end NumberField.IsOrder

namespace NumberField.IsOrder

/--
[isFractionRing](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Order.lean)
-/
public theorem isFractionRing
  [Field K] [NumberField K]
  {O : Subalgebra ℤ K}
-- given
  (h : NumberField.IsOrder K O) :
-- imply
  IsFractionRing O K :=
-- proof
  h.2

end NumberField.IsOrder

namespace NumberField.IsOrder

/--
[exists_div_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Order.lean)
-/
public theorem exists_div_eq
  [Field K] [NumberField K]
  {O : Subalgebra ℤ K}
  {x : K}
-- given
  (hO : NumberField.IsOrder K O) :
-- imply
  ∃ (a b : O), b ≠ 0 ∧ (a : K) / (b : K) = x := by
-- proof
  let _inst : IsFractionRing O K := hO.isFractionRing
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := O) x
  exact ⟨a, b, mem_nonZeroDivisors_iff_ne_zero.mp hb, by simpa using hab⟩

end NumberField.IsOrder

/--
[NumberField.isOrder_integralClosure](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Order.lean)
-/
public theorem NumberField.isOrder_integralClosure
  [Field K] [NumberField K] :
-- imply
  NumberField.IsOrder K (integralClosure ℤ K) := by
-- proof
  constructor
  · exact le_rfl
  · exact integralClosure.isFractionRing_of_finite_extension ℚ _


-- created on 2026-10-20
-- updated on 2026-10-28
