import Lemma.AbsoluteValue.Norm.eq.UFn
import Lemma.AbsoluteValue.IsNontrivial.is.Any_Lt1Norm
open AbsoluteValue


/--
[AbsoluteValue_Completion_norm_coe_and_exists_one_lt_norm](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AbsoluteValue_Completion_norm_coe_and_exists_one_lt_norm.lean)
-/
@[main]
private lemma main
-- given
  [Field K]
  (v : AbsoluteValue K ℝ) :
-- imply
  (∀ x : K, ‖(x : v.Completion)‖ = v x) ∧ (v.IsNontrivial → ∃ x : v.Completion, 1 < ‖x‖) :=
-- proof
  ⟨Norm.eq.UFn v, Any_Lt1Norm.of.IsNontrivial⟩


-- created on 2026-09-19
