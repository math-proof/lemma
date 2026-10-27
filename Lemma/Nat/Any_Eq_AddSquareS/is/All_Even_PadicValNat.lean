import Mathlib
import Initialize.Tactic.Attr.Basic


namespace FactorizationNoetherian

/--
[sum_of_two_squares_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/FactorizationNoetherian.lean)
-/
@[path]
private lemma sum_of_two_squares_iff
  {n : ℕ} :
-- imply
  (∃ x y : ℕ, n = x ^ 2 + y ^ 2) ↔ ∀ q ∈ n.primeFactors, q % 4 = 3 → Even (padicValNat q n) :=
-- proof
  Nat.eq_sq_add_sq_iff

end FactorizationNoetherian


-- created on 2026-10-24
