import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.WardGeneralizedBinomial
open scoped BigOperators
open MetaMathlibExt


/--
[wardUnitsCarry_eq_div](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/WardGeneralizedBinomial.lean)
-/
@[path]
private lemma wardUnitsCarry_eq_div_eq
  {b n m : ℕ} :
-- imply
  wardUnitsCarry b n m = (n % b + m % b) / b := by
-- proof
  apply MetaMathlibExt.wardUnitsCarry_eq_div b n m

/--
[wardGeneralizedBinomialCoefficient_eq_prod_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/WardGeneralizedBinomial.lean)
-/
@[path]
private lemma wardGeneralizedBinomialCoefficient_eq_prod_Icc_eq
  [CommMonoid R]
  {s : ℕ → R}
  {n m : ℕ} :
-- imply
  wardGeneralizedBinomialCoefficient s n m =
      ∏ b ∈ Finset.Icc 2 (n + m), s b ^ ((n % b + m % b) / b) := by
-- proof
  apply MetaMathlibExt.wardGeneralizedBinomialCoefficient_eq_prod_Icc s n m


-- created on 2026-10-20
