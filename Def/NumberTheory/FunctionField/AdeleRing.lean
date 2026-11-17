/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FunctionField/AdeleRing.lean -/

module

public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Set.Algebra.RestrictedProduct.Basic

@[expose] public section

open scoped RestrictedProduct

/-!
# Adèle rings of function fields

This file defines the restricted-product adèle ring attached to a field and a family of
valuation subrings.
-/


/-- The adèle ring associated to a field `F`, a type `P` of places, and valuation subrings
`O p`. Its elements belong to `O p` for all but finitely many `p`. -/
def FunctionFieldAdeleRing (F : Type*) [Field F] (P : Type*)
    (O : P → ValuationSubring F) : Type _ :=
  Πʳ p : P, [F, O p]
