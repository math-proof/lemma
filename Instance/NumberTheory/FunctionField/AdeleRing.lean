/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FunctionField/AdeleRing.lean -/

import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Def.NumberTheory.FunctionField.AdeleRing
open scoped RestrictedProduct

/-!
# Adèle rings of function fields

This file defines the restricted-product adèle ring attached to a field and a family of
valuation subrings.
-/


namespace FunctionFieldAdeleRing

variable {F : Type*} [Field F] {P : Type*} {O : P → ValuationSubring F}

noncomputable instance : CommRing (FunctionFieldAdeleRing F P O) :=
  inferInstanceAs (CommRing (Πʳ p : P, [F, O p]))

instance : DFunLike (FunctionFieldAdeleRing F P O) P (fun _ ↦ F) :=
  inferInstanceAs (DFunLike (Πʳ p : P, [F, O p]) P (fun _ ↦ F))

end FunctionFieldAdeleRing
