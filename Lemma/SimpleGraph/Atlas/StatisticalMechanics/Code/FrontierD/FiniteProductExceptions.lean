import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FiniteProductExceptions
open StatMech StatMech.FrontierD


/--
[pow_mul_pow_le_prod_of_exception_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteProductExceptions.lean)
-/
@[path]
private lemma pow_mul_pow_le_prod_of_exception_card_eq
  [Fintype ι]
  [DecidableEq ι]
  {bad : Finset ι}
  {D : Nat}
  {a b : Real}
-- given
  (ha : 0 < a)
  (ha1 : a <= 1)
  (hb : 0 < b)
  (hb1 : b <= 1)
  (hcard : bad.card <= D)
  (F : ι -> Real)
  (hall : ∀ i, b <= F i)
  (hbulk : ∀ i, i ∉ bad -> a <= F i) :
-- imply
  b ^ D * a ^ Fintype.card ι <= ∏ i, F i := by
-- proof
  apply StatMech.FrontierD.pow_mul_pow_le_prod_of_exception_card bad D ha ha1 hb hb1 hcard F hall hbulk


-- created on 2026-10-23
