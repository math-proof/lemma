import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.GenocchiNumber
import Lemma.Nat.GenocchiNumber
import Lemma.Finset.Enumerative.GarabedianBernoulliStirling
import Def.Combinatorics.Enumerative.GarabedianBernoulliStirling
open scoped BigOperators


namespace MetaMathlibExt

/--
[genocchiNumber_eq_stirlingSecond_sum_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/GarabedianGenocchiFormula.lean)
-/
@[path]
lemma genocchiNumber_eq_stirlingSecond_sum_general
  {n : ℕ} :
-- imply
  genocchiNumber n =
    (n : ℚ) * ∑ k ∈ Finset.Icc 1 n,
    (-1 : ℚ) ^ (n - k) * (Nat.factorial (k - 1) : ℚ) * (Nat.stirlingSecond n k : ℚ) /
    (2 : ℚ) ^ (k - 1) :=
-- proof
  (genocchiNumber_eq_bernoulli n).trans (garabedian_genocchi_formula_general n)
set_option linter.unusedVariables false in

end MetaMathlibExt

namespace MetaMathlibExt

/--
[genocchiNumber_eq_stirlingSecond_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/GarabedianGenocchiFormula.lean)
-/
@[path]
lemma genocchiNumber_eq_stirlingSecond_sum
  {n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  genocchiNumber n =
    (n : ℚ) * ∑ k ∈ Finset.Icc 1 n,
    (-1 : ℚ) ^ (n - k) * (Nat.factorial (k - 1) : ℚ) * (Nat.stirlingSecond n k : ℚ) /
    (2 : ℚ) ^ (k - 1) :=
-- proof
  genocchiNumber_eq_stirlingSecond_sum_general n
end



-- created on 2026-10-20
-- updated on 2026-10-26
