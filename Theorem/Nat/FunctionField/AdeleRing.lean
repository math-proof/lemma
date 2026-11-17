module

public import Mathlib
public import Instance.NumberTheory.FunctionField.AdeleRing

public section

open scoped RestrictedProduct
open FunctionFieldAdeleRing


namespace FunctionFieldAdeleRing

/--
[ext](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FunctionField/AdeleRing.lean)
-/
public theorem ext
  [Field F]
  {O : P → ValuationSubring F}
  {a b : FunctionFieldAdeleRing F P O}
-- given
  (h : ∀ p, a p = b p) :
-- imply
  a = b :=
-- proof
  Subtype.ext <| funext h

end FunctionFieldAdeleRing

namespace FunctionFieldAdeleRing

/--
[mem_valuationSubring_cofinitely](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FunctionField/AdeleRing.lean)
-/
public theorem mem_valuationSubring_cofinitely
  [Field F]
  {O : P → ValuationSubring F}
  {a : FunctionFieldAdeleRing F P O} :
-- imply
  ∀ᶠ p in Filter.cofinite, a p ∈ O p :=
-- proof
  a.2

end FunctionFieldAdeleRing


-- created on 2026-10-20
-- updated on 2026-10-26
