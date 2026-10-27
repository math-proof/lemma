import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.NumberTheoryI.code.Chapter1.Valuations.Part2


/--
[valuationRing_iff_forall_mem_or_inv_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter1/Valuations.lean)
-/
@[path]
lemma valuationRing_iff_forall_mem_or_inv_mem
  {A : Type*}
  [CommRing A]
  [IsDomain A] :
-- imply
  ValuationRing A ↔ ∀ x : FractionRing A, IsLocalization.IsInteger A x ∨ IsLocalization.IsInteger A x⁻¹ :=
-- proof
  ValuationRing.iff_isInteger_or_isInteger A (FractionRing A)

/--
[isNonarchimedean_discreteValuationAbsoluteValueFun](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter1/Valuations.lean)
-/
@[path]
private lemma isNonarchimedean_discreteValuationAbsoluteValueFun_eq
  [Field k]
  {v : Valuation k (WithZero (Multiplicative ℤ))}
  {c : NNReal}
-- given
  (hc : 1 < c) :
-- imply
  IsNonarchimedean (discreteValuationAbsoluteValueFun v (ne_zero_of_lt hc)) := by
-- proof
  apply isNonarchimedean_discreteValuationAbsoluteValueFun v hc


-- created on 2026-10-23
