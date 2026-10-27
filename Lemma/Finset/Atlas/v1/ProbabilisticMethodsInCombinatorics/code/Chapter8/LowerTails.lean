import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter8.LowerTails
open Real Janson JansonInequality
open Janson


namespace Janson

/--
[JansonSetup.mu_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter8/LowerTails.lean)
-/
@[path]
lemma JansonSetup.mu_nonneg
  {J : JansonSetup} :
-- imply
  0 ≤ J.mu :=
-- proof
  Finset.sum_nonneg fun i _ => Finset.prod_nonneg fun j _ => J.prob_nonneg j

end Janson

namespace Janson

/--
[JansonSetup.delta_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter8/LowerTails.lean)
-/
@[path]
lemma JansonSetup.delta_nonneg
  {J : JansonSetup} :
-- imply
  0 ≤ J.delta := by
-- proof
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact Finset.prod_nonneg fun l _ => J.prob_nonneg l
  · exact le_refl 0

end Janson

namespace Janson

/--
[JansonSetup.probSubset_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter8/LowerTails.lean)
-/
@[path]
lemma JansonSetup.probSubset_nonneg
  {J : JansonSetup}
  {T : Finset (Fin J.N)} :
-- imply
  0 ≤ J.probSubset T := by
-- proof
  unfold JansonSetup.probSubset
  apply mul_nonneg
  · exact Finset.prod_nonneg (fun i _ => J.prob_nonneg i)
  · exact Finset.prod_nonneg (fun i _ => by linarith [J.prob_le_one i])

end Janson

namespace Janson

/--
[JansonSetup.sum_probSubset_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter8/LowerTails.lean)
-/
@[path]
lemma JansonSetup.sum_probSubset_eq_one
  {J : JansonSetup} :
-- imply
  ∑ T ∈ Finset.powerset Finset.univ, J.probSubset T = 1 := by
-- proof
  unfold JansonSetup.probSubset
  have key := Finset.prod_add (fun i : Fin J.N => J.prob i) (fun i : Fin J.N => 1 - J.prob i)
    (Finset.univ : Finset (Fin J.N))
  simp only [add_sub_cancel] at key
  rwa [Finset.prod_const_one] at key
end Janson
namespace JansonInequality
open Janson


namespace JansonInequality

/--
[one_sub_exp_neg_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter8/LowerTails.lean)
-/
@[path]
lemma one_sub_exp_neg_le
  {l : ℝ}
-- given
  (_hl : 0 ≤ l) :
-- imply
  1 - Real.exp (-l) ≤ l := by
-- proof
  linarith [add_one_le_exp (x := -l)]

end JansonInequality

namespace JansonInequality

/--
[one_sub_exp_neg_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter8/LowerTails.lean)
-/
@[path]
lemma one_sub_exp_neg_nonneg
  {l : ℝ}
-- given
  (hl : 0 ≤ l) :
-- imply
  0 ≤ 1 - Real.exp (-l) := by
-- proof
  linarith [Real.exp_le_one_iff.mpr (neg_nonpos.mpr hl)]

end JansonInequality

namespace JansonInequality

/--
[le_one_sub_exp_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter8/LowerTails.lean)
-/
@[path]
lemma le_one_sub_exp_neg
  {l : ℝ}
-- given
  (hl : 0 ≤ l) :
-- imply
  l - l ^ 2 / 2 ≤ 1 - Real.exp (-l) := by
-- proof
  suffices h : Real.exp (-l) ≤ 1 - l + l ^ 2 / 2 by linarith
  have hquad : 1 + l + l ^ 2 / 2 ≤ Real.exp l := Real.quadratic_le_exp_of_nonneg hl
  rw [Real.exp_neg]
  have hpos : 0 < 1 + l + l ^ 2 / 2 := by positivity
  have hinv_le : (Real.exp l)⁻¹ ≤ (1 + l + l ^ 2 / 2)⁻¹ := inv_anti₀ hpos hquad
  have hrhs_pos : 0 < 1 - l + l ^ 2 / 2 := by nlinarith [sq_nonneg l]
  have hfinal : (1 + l + l ^ 2 / 2)⁻¹ ≤ 1 - l + l ^ 2 / 2 := by
    rw [inv_le_comm₀ hpos hrhs_pos]
    calc (1 - l + l ^ 2 / 2)⁻¹
      = 1 / (1 - l + l ^ 2 / 2) := (one_div _).symm
      _ ≤ (1 + l + l ^ 2 / 2) := by
        rw [div_le_iff₀ hrhs_pos]
        nlinarith [sq_nonneg (l ^ 2)]
  linarith

end JansonInequality

namespace JansonInequality

/--
[optimal_lambda_value](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter8/LowerTails.lean)
-/
@[path]
lemma optimal_lambda_value
  {mu Delta t : ℝ}
-- given
  (hpos : 0 < mu + Delta) :
-- imply
  -(t / (mu + Delta)) * t + (t / (mu + Delta)) ^ 2 * (mu + Delta) / 2 = -(t ^ 2 / (2 * (mu + Delta))) := by
-- proof
  field_simp
  ring

end JansonInequality

namespace JansonInequality

/--
[janson_III_prob_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter8/LowerTails.lean)
-/
@[path]
lemma janson_III_prob_le_one
  {J : JansonSetup}
  {t : ℝ} :
-- imply
  J.probLowerTail t ≤ 1 := by
-- proof
  suffices h : J.probLowerTail t ≤ ∑ T ∈ Finset.powerset Finset.univ, J.probSubset T by
    linarith [J.sum_probSubset_eq_one]
  unfold JansonSetup.probLowerTail
  apply Finset.sum_le_sum
  intro T _
  split_ifs
  · exact le_refl _
  · exact J.probSubset_nonneg T
/-- **Janson inequality III** (Theorem 8.2.2, lower tail). For any $0 \leq t \leq \mu$,
$\Pr(X \leq \mu - t) \leq \exp\!\left(-\dfrac{t^2}{2(\mu + \Delta)}\right)$. -/

end JansonInequality


-- created on 2026-10-23
