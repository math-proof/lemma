import Mathlib
import sympy.Basic
open Subgroup MulAction ConjClasses


namespace Definitions
end Definitions
namespace ClassEquation

/--
[isPGroup_iff_card](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/ClassEquation.lean)
-/
@[path]
private lemma isPGroup_iff_card
  [Group G]
  [Finite G]
  {p : ℕ} [Fact (Nat.Prime p)] :
-- imply
  IsPGroup p G ↔ ∃ n : ℕ, Nat.card G = p ^ n :=
-- proof
  IsPGroup.iff_card

end ClassEquation

namespace ClassEquation

/--
[group_of_order_p_sq_abelian](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/ClassEquation.lean)
-/
@[path]
private lemma group_of_order_p_sq_abelian
  [Group G]
  {p : ℕ} [Fact (Nat.Prime p)]
  {a b : G}
-- given
  (hG : Nat.card G = p ^ 2) :
-- imply
  a * b = b * a :=
-- proof
  (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p) (G := G) hG).is_comm.comm a b

end ClassEquation


-- created on 2026-10-24
