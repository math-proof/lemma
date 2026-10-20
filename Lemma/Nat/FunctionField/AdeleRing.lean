import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.FunctionField.AdeleRing
open scoped RestrictedProduct
open FunctionFieldAdeleRing


/--
[ext](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FunctionField/AdeleRing.lean)
-/
@[path]
private lemma ext_eq
  [Field F]
  {O : P → ValuationSubring F}
  {a b : FunctionFieldAdeleRing F P O}
-- given
  (h : ∀ p, a p = b p) :
-- imply
  a = b := by
-- proof
  apply FunctionFieldAdeleRing.ext h

/--
[mem_valuationSubring_cofinitely](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FunctionField/AdeleRing.lean)
-/
@[path]
private lemma mem_valuationSubring_cofinitely_eq
  [Field F]
  {O : P → ValuationSubring F}
  {a : FunctionFieldAdeleRing F P O} :
-- imply
  ∀ᶠ p in Filter.cofinite, a p ∈ O p := by
-- proof
  apply FunctionFieldAdeleRing.mem_valuationSubring_cofinitely a


-- created on 2026-10-20
