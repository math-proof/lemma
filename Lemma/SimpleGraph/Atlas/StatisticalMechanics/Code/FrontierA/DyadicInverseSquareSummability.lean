import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.DyadicInverseSquareSummability.Part4
open Filter Finset Set Topology StatMech StatMech.FrontierA


/--
[size_le_two_pow_dyadicUpperLevel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/DyadicInverseSquareSummability.lean)
-/
@[path]
private lemma size_le_two_pow_dyadicUpperLevel_eq
  {size : Q → Real}
  {q : Q} :
-- imply
  size q ≤ (2 : Real) ^ dyadicUpperLevel size q := by
-- proof
  apply StatMech.FrontierA.size_le_two_pow_dyadicUpperLevel size q

/--
[two_pow_lt_size_of_lt_dyadicUpperLevel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/DyadicInverseSquareSummability.lean)
-/
@[path]
private lemma two_pow_lt_size_of_lt_dyadicUpperLevel_eq
  {size : Q → Real}
  {q : Q}
  {n : Nat}
-- given
  (hn : n < dyadicUpperLevel size q) :
-- imply
  (2 : Real) ^ n < size q := by
-- proof
  apply StatMech.FrontierA.two_pow_lt_size_of_lt_dyadicUpperLevel size q hn

/--
[summable_inverse_sq_of_linear_sublevel_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/DyadicInverseSquareSummability.lean)
-/
@[path]
private lemma summable_inverse_sq_of_linear_sublevel_count_eq
  [Countable Q]
  {size : Q → Real}
  {A B : Real}
-- given
  (hsize : ∀ q, 1 ≤ size q)
  (hfinite : ∀ R : Real, Set.Finite {q | size q ≤ R})
  (hA : 0 ≤ A)
  (hB : 0 ≤ B)
  (hcount : ∀ R : Real, 1 ≤ R → (Nat.card {q : Q // size q ≤ R} : Real) ≤ A + B * R) :
-- imply
  Summable (fun q : Q => 1 / size q ^ 2) := by
-- proof
  apply StatMech.FrontierA.summable_inverse_sq_of_linear_sublevel_count size hsize hfinite hA hB hcount

/--
[tsum_inverse_sq_le_of_linear_sublevel_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/DyadicInverseSquareSummability.lean)
-/
@[path]
private lemma tsum_inverse_sq_le_of_linear_sublevel_count_eq
  [Countable Q]
  {A B : Real}
-- given
  (size : Q -> Real)
  (hsize : forall q, 1 <= size q)
  (hfinite : forall R : Real, Set.Finite {q | size q <= R})
  (hA : 0 <= A)
  (hB : 0 <= B)
  (hcount : forall R : Real, 1 <= R -> (Nat.card {q : Q // size q <= R} : Real) <= A + B * R) :
-- imply
  ∑' q : Q, 1 / size q ^ 2 <= (16 / 3 : Real) * A + 8 * B := by
-- proof
  apply StatMech.FrontierA.tsum_inverse_sq_le_of_linear_sublevel_count size hsize hfinite hA hB hcount

/--
[tsum_inverse_sq_tail_le_of_linear_sublevel_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/DyadicInverseSquareSummability.lean)
-/
@[path]
private lemma tsum_inverse_sq_tail_le_of_linear_sublevel_count_eq
  [Countable Q]
  {A B : Real}
  {R : Real}
-- given
  (size : Q -> Real)
  (hfinite : forall S : Real, Set.Finite {q | size q <= S})
  (hA : 0 <= A)
  (hB : 0 <= B)
  (hcount : forall S : Real, 1 <= S -> (Nat.card {q : Q // size q <= S} : Real) <= A + B * S)
  (hR : 1 <= R) :
-- imply
  ∑' q : {q : Q // R < size q}, 1 / size q.1 ^ 2 <= (16 / 3 : Real) * A / R ^ 2 + 8 * B / R := by
-- proof
  apply StatMech.FrontierA.tsum_inverse_sq_tail_le_of_linear_sublevel_count size hfinite hA hB hcount R hR

/--
[tsum_two_mul_radius_div_sq_add_sq_le_of_linear_sublevel_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/DyadicInverseSquareSummability.lean)
-/
@[path]
private lemma tsum_two_mul_radius_div_sq_add_sq_le_of_linear_sublevel_count_eq
  [Countable Q]
  {A B : Real}
  {R : Real}
-- given
  (size : Q -> Real)
  (hsize : forall q, 1 <= size q)
  (hfinite : forall S : Real, Set.Finite {q | size q <= S})
  (hA : 0 <= A)
  (hB : 0 <= B)
  (hcount : forall S : Real, 1 <= S -> (Nat.card {q : Q // size q <= S} : Real) <= A + B * S)
  (hR : 1 <= R) :
-- imply
  ∑' q : Q, 2 * R / (size q ^ 2 + R ^ 2) <= 13 * A + 18 * B := by
-- proof
  apply StatMech.FrontierA.tsum_two_mul_radius_div_sq_add_sq_le_of_linear_sublevel_count size hsize hfinite hA hB hcount R hR


-- created on 2026-10-23
