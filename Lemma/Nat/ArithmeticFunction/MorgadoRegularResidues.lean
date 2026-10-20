import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.ArithmeticFunction.MorgadoRegularResidues
open scoped BigOperators
open MetaMathlibExt


/--
[ncard_regular_eq_sum_totient_unitaryDivisors](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/MorgadoRegularResidues.lean)
-/
@[path]
private lemma ncard_regular_eq_sum_totient_unitaryDivisors_eq
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  Set.ncard {m : ZMod n | ∃ x : ZMod n, m ^ 2 * x = m} =
    ∑ d ∈ n.unitaryDivisors, Nat.totient d := by
-- proof
  apply MetaMathlibExt.ncard_regular_eq_sum_totient_unitaryDivisors n hn

/--
[morgado_card_regular_modulo](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/MorgadoRegularResidues.lean)
-/
@[path]
private lemma morgado_card_regular_modulo_eq
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  Set.ncard {m : ZMod n | ∃ x : ZMod n, m ^ 2 * x = m} =
    ∑ d ∈ n.divisors.filter (fun d => Nat.Coprime d (n / d)), Nat.totient d := by
-- proof
  apply MetaMathlibExt.morgado_card_regular_modulo n hn


-- created on 2026-10-20
