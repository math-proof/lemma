/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/FunctionField/AdeleRing.lean -/


import Instance.NumberTheory.FunctionField.AdeleRing
import Lemma.Nat.FunctionField.AdeleRing
open scoped RestrictedProduct


namespace FunctionFieldAdeleRing

variable {F : Type*} [Field F] {P : Type*} {O : P → ValuationSubring F}

example (p : P) : (0 : FunctionFieldAdeleRing F P O) p = 0 := by
  rfl

example (a : FunctionFieldAdeleRing F P O) :
    ∀ᶠ p in Filter.cofinite, a p ∈ O p :=
  mem_valuationSubring_cofinitely a

example {a b : FunctionFieldAdeleRing F P O} (h : ∀ p, a p = b p) : a = b :=
  ext h

end FunctionFieldAdeleRing
