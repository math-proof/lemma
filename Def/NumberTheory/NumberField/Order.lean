/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Order.lean -/

import Mathlib.NumberTheory.NumberField.Basic


/-! An order in a number field `K` is a `ℤ`-subalgebra of `K` contained in the
integral closure `integralClosure ℤ K = 𝓞 K` whose fraction field is `K`.
This formalizes arXiv:2608.02983v1, TypesofQuartic25.tex line 136:
> Let K be an algebraic number field and O_K its ring of integers, and O an order
> in O_K (a subring of O_K with quotient field K). -/
def NumberField.IsOrder (K : Type*) [Field K] [NumberField K] (O : Subalgebra ℤ K) : Prop :=
  O ≤ integralClosure ℤ K ∧ IsFractionRing O K

