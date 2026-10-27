import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Inequalities.OSSS.Part6
open Finset StatMech StatMech.OSSS StatMech.OSSS.DecisionTree


/--
[pt_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma pt_self_eq
  [Fintype E]
  [DecidableEq E]
  {b : Bool} :
-- imply
  pt b b = 1 := by
-- proof
  apply StatMech.OSSS.pt_self b

/--
[pt_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma pt_apply_eq
  [Fintype E]
  [DecidableEq E]
  {b c : Bool} :
-- imply
  pt b c = if c = b then 1 else 0 := by
-- proof
  apply StatMech.OSSS.pt_apply b c

/--
[weight_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma weight_factor_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {e : E}
  {ω : ConfigSpace E} :
-- imply
  weight ν ω = ν e (ω e) * ∏ e' ∈ univ.erase e, ν e' (ω e') := by
-- proof
  apply StatMech.OSSS.weight_factor ν e ω

/--
[restrict_update](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma restrict_update_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {e : E}
  {ω : ConfigSpace E}
  {b : Bool} :
-- imply
  (∏ e' ∈ univ.erase e, ν e' (Function.update ω e b e')) = ∏ e' ∈ univ.erase e, ν e' (ω e') := by
-- proof
  apply StatMech.OSSS.restrict_update ν e ω b

/--
[weight_cond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma weight_cond_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {e : E}
  {b : Bool}
  {ω : ConfigSpace E} :
-- imply
  weight (Function.update ν e (pt b)) ω = pt b (ω e) * ∏ e' ∈ univ.erase e, ν e' (ω e') := by
-- proof
  apply StatMech.OSSS.weight_cond ν e b ω

/--
[expect_cond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma expect_cond_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {e : E}
  {g : ConfigSpace E → ℝ} :
-- imply
  expect ν g = ν e true * expect (Function.update ν e (pt true)) g + ν e false * expect (Function.update ν e (pt false)) g := by
-- proof
  apply StatMech.OSSS.expect_cond ν e g

/--
[expect_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma expect_add_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
-- given
  (g h : ConfigSpace E → ℝ) :
-- imply
  expect ν (fun ω => g ω + h ω) = expect ν g + expect ν h := by
-- proof
  apply StatMech.OSSS.expect_add ν g h

/--
[expect_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma expect_sub_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
-- given
  (g h : ConfigSpace E → ℝ) :
-- imply
  expect ν (fun ω => g ω - h ω) = expect ν g - expect ν h := by
-- proof
  apply StatMech.OSSS.expect_sub ν g h

/--
[expect_const_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma expect_const_mul_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {c : ℝ}
  {g : ConfigSpace E → ℝ} :
-- imply
  expect ν (fun ω => c * g ω) = c * expect ν g := by
-- proof
  apply StatMech.OSSS.expect_const_mul ν c g

/--
[expect_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma expect_mono_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {g h : ConfigSpace E → ℝ}
-- given
  (hν : IsProbWeight ν)
  (hgh : ∀ ω, g ω ≤ h ω) :
-- imply
  expect ν g ≤ expect ν h := by
-- proof
  apply StatMech.OSSS.expect_mono hν hgh

/--
[expect_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma expect_one_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
-- given
  (hν : IsProbWeight ν) :
-- imply
  expect ν (fun _ => 1) = 1 := by
-- proof
  apply StatMech.OSSS.expect_one hν

/--
[condMean_setOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma condMean_setOpen_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {e : E}
  {g : ConfigSpace E → ℝ}
  {ω : ConfigSpace E} :
-- imply
  condMean ν e g (setOpen e ω) = condMean ν e g ω := by
-- proof
  apply StatMech.OSSS.condMean_setOpen ν e g ω

/--
[condMean_setClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma condMean_setClosed_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {e : E}
  {g : ConfigSpace E → ℝ}
  {ω : ConfigSpace E} :
-- imply
  condMean ν e g (setClosed e ω) = condMean ν e g ω := by
-- proof
  apply StatMech.OSSS.condMean_setClosed ν e g ω

/--
[condMean_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma condMean_eq_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {e : E}
  {g : ConfigSpace E → ℝ}
  {ω : ConfigSpace E} :
-- imply
  condMean ν e g ω = ν e true * g (setOpen e ω) + ν e false * g (setClosed e ω) := by
-- proof
  apply StatMech.OSSS.condMean_eq ν e g ω

/--
[evalR_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma evalR_le_one_eq
  [Fintype E]
  [DecidableEq E]
  {T : DecisionTree E}
  {ω : ConfigSpace E} :
-- imply
  T.evalR ω ≤ 1 := by
-- proof
  apply StatMech.OSSS.DecisionTree.evalR_le_one T ω

/--
[evalR_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma evalR_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {T : DecisionTree E}
  {ω : ConfigSpace E} :
-- imply
  0 ≤ T.evalR ω := by
-- proof
  apply StatMech.OSSS.DecisionTree.evalR_nonneg T ω

/--
[abs_evalR_diff_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma abs_evalR_diff_le_one_eq
  [Fintype E]
  [DecidableEq E]
  {T : DecisionTree E}
  {e : E}
  {ω : ConfigSpace E} :
-- imply
  |T.evalR (setOpen e ω) - T.evalR (setClosed e ω)| ≤ 1 := by
-- proof
  apply StatMech.OSSS.DecisionTree.abs_evalR_diff_le_one T e ω

/--
[expect_cond_forces](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma expect_cond_forces_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {e : E}
  {b : Bool}
-- given
  (h : ConfigSpace E → ℝ) :
-- imply
  expect (Function.update ν e (pt b)) h = expect (Function.update ν e (pt b)) (fun ω => h (Function.update ω e b)) := by
-- proof
  apply StatMech.OSSS.expect_cond_forces ν e b h

/--
[reveal_root](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma reveal_root_eq
  [Fintype E]
  [DecidableEq E]
  {e : E}
  {t f : DecisionTree E}
-- given
  (hν : IsProbWeight ν) :
-- imply
  reveal ν (.node e t f) e = 1 := by
-- proof
  apply StatMech.OSSS.reveal_root hν e t f

/--
[mem_queried_node_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma mem_queried_node_iff_eq
  [Fintype E]
  [DecidableEq E]
  {e i : E}
  {t f : DecisionTree E}
  {ω : ConfigSpace E}
  {b : Bool}
-- given
  (hi : i ≠ e)
  (h : ω e = b) :
-- imply
  (i ∈ (DecisionTree.node e t f).queried ω) ↔ (i ∈ (if b then t else f).queried ω) := by
-- proof
  apply StatMech.OSSS.mem_queried_node_iff e i hi t f ω b h

/--
[expect_indQ_node_cond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma expect_indQ_node_cond_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {e i : E}
  {b : Bool}
  {t f : DecisionTree E}
-- given
  (hi : i ≠ e) :
-- imply
  expect (Function.update ν e (pt b)) (fun ω => if i ∈ (DecisionTree.node e t f).queried ω then (1:ℝ) else 0) = expect (Function.update ν e (pt b)) (fun ω => if i ∈ (if b then t else f).queried ω then (1:ℝ) else 0) := by
-- proof
  apply StatMech.OSSS.expect_indQ_node_cond ν e i hi b t f

/--
[reveal_node_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma reveal_node_ne_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {e i : E}
  {t f : DecisionTree E}
-- given
  (hi : i ≠ e) :
-- imply
  reveal ν (.node e t f) i = ν e true * reveal (Function.update ν e (pt true)) t i + ν e false * reveal (Function.update ν e (pt false)) f i := by
-- proof
  apply StatMech.OSSS.reveal_node_ne ν e i hi t f

/--
[infl_cond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma infl_cond_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {e : E}
  {i : E}
-- given
  (h : ConfigSpace E → ℝ) :
-- imply
  infl ν h i = ν e true * infl (Function.update ν e (pt true)) h i + ν e false * infl (Function.update ν e (pt false)) h i := by
-- proof
  apply StatMech.OSSS.infl_cond ν e h i

/--
[infl_condMean_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma infl_condMean_self_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {e : E}
  {g : ConfigSpace E → ℝ} :
-- imply
  infl ν (condMean ν e g) e = 0 := by
-- proof
  apply StatMech.OSSS.infl_condMean_self ν e g

/--
[flipAt_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma flipAt_involutive_eq
  [Fintype E]
  [DecidableEq E]
  {e : E} :
-- imply
  Function.Involutive (flipAt e) := by
-- proof
  apply StatMech.OSSS.flipAt_involutive e

/--
[flipAt_eval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma flipAt_eval_eq
  [Fintype E]
  [DecidableEq E]
  {e : E}
  {ω : ConfigSpace E} :
-- imply
  flipAt e ω e = !(ω e) := by
-- proof
  apply StatMech.OSSS.flipAt_eval e ω

/--
[flipAt_eval_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma flipAt_eval_ne_eq
  [Fintype E]
  [DecidableEq E]
  {e e' : E}
  {ω : ConfigSpace E}
-- given
  (he : e' ≠ e) :
-- imply
  flipAt e ω e' = ω e' := by
-- proof
  apply StatMech.OSSS.flipAt_eval_ne e e' he ω

/--
[pt_not](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma pt_not_eq
  [Fintype E]
  [DecidableEq E]
  {b c : Bool} :
-- imply
  pt b (!c) = pt (!b) c := by
-- proof
  apply StatMech.OSSS.pt_not b c

/--
[expect_cond_indep_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma expect_cond_indep_flip_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {e : E}
  {b : Bool}
  {k : ConfigSpace E → ℝ}
-- given
  (hk : ∀ ω, k (flipAt e ω) = k ω) :
-- imply
  expect (Function.update ν e (pt b)) k = expect (Function.update ν e (pt (!b))) k := by
-- proof
  apply StatMech.OSSS.expect_cond_indep_flip ν e b k hk

/--
[setOpen_flipAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma setOpen_flipAt_eq
  [Fintype E]
  [DecidableEq E]
  {e : E}
  {ω : ConfigSpace E} :
-- imply
  setOpen e (flipAt e ω) = setOpen e ω := by
-- proof
  apply StatMech.OSSS.setOpen_flipAt e ω

/--
[setClosed_flipAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma setClosed_flipAt_eq
  [Fintype E]
  [DecidableEq E]
  {e : E}
  {ω : ConfigSpace E} :
-- imply
  setClosed e (flipAt e ω) = setClosed e ω := by
-- proof
  apply StatMech.OSSS.setClosed_flipAt e ω

/--
[expect_condT_setOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma expect_condT_setOpen_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {e : E}
-- given
  (h : ConfigSpace E → ℝ) :
-- imply
  expect (Function.update ν e (pt true)) (fun ω => h (setOpen e ω)) = expect (Function.update ν e (pt true)) h := by
-- proof
  apply StatMech.OSSS.expect_condT_setOpen ν e h

/--
[expect_setOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma expect_setOpen_eq
  [Fintype E]
  [DecidableEq E]
  {e : E}
-- given
  (hν : IsProbWeight ν)
  (h : ConfigSpace E → ℝ) :
-- imply
  expect ν (fun ω => h (setOpen e ω)) = expect (Function.update ν e (pt true)) h := by
-- proof
  apply StatMech.OSSS.expect_setOpen hν e h

/--
[expect_condF_setClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma expect_condF_setClosed_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {e : E}
-- given
  (h : ConfigSpace E → ℝ) :
-- imply
  expect (Function.update ν e (pt false)) (fun ω => h (setClosed e ω)) = expect (Function.update ν e (pt false)) h := by
-- proof
  apply StatMech.OSSS.expect_condF_setClosed ν e h

/--
[expect_setClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma expect_setClosed_eq
  [Fintype E]
  [DecidableEq E]
  {e : E}
-- given
  (hν : IsProbWeight ν)
  (h : ConfigSpace E → ℝ) :
-- imply
  expect ν (fun ω => h (setClosed e ω)) = expect (Function.update ν e (pt false)) h := by
-- proof
  apply StatMech.OSSS.expect_setClosed hν e h

/--
[setOpen_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma setOpen_comm_eq
  [Fintype E]
  [DecidableEq E]
  {e i : E}
  {ω : ConfigSpace E}
-- given
  (h : i ≠ e) :
-- imply
  setOpen e (setOpen i ω) = setOpen i (setOpen e ω) := by
-- proof
  apply StatMech.OSSS.setOpen_comm h ω

/--
[setClosed_setOpen_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma setClosed_setOpen_comm_eq
  [Fintype E]
  [DecidableEq E]
  {e i : E}
  {ω : ConfigSpace E}
-- given
  (h : i ≠ e) :
-- imply
  setClosed e (setOpen i ω) = setOpen i (setClosed e ω) := by
-- proof
  apply StatMech.OSSS.setClosed_setOpen_comm h ω

/--
[setOpen_setClosed_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma setOpen_setClosed_comm_eq
  [Fintype E]
  [DecidableEq E]
  {e i : E}
  {ω : ConfigSpace E}
-- given
  (h : i ≠ e) :
-- imply
  setOpen e (setClosed i ω) = setClosed i (setOpen e ω) := by
-- proof
  apply StatMech.OSSS.setOpen_setClosed_comm h ω

/--
[setClosed_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma setClosed_comm_eq
  [Fintype E]
  [DecidableEq E]
  {e i : E}
  {ω : ConfigSpace E}
-- given
  (h : i ≠ e) :
-- imply
  setClosed e (setClosed i ω) = setClosed i (setClosed e ω) := by
-- proof
  apply StatMech.OSSS.setClosed_comm h ω

/--
[infl_eq_expect_H](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma infl_eq_expect_H_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {g : ConfigSpace E → ℝ}
  {i : E} :
-- imply
  infl ν g i = expect ν (fun ω => |g (setOpen i ω) - g (setClosed i ω)|) := by
-- proof
  apply StatMech.OSSS.infl_eq_expect_H ν g i

/--
[infl_condMean_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma infl_condMean_le_eq
  [Fintype E]
  [DecidableEq E]
  {e i : E}
  {g : ConfigSpace E → ℝ}
-- given
  (hν : IsProbWeight ν)
  (hi : i ≠ e) :
-- imply
  infl ν (condMean ν e g) i ≤ infl ν g i := by
-- proof
  apply StatMech.OSSS.infl_condMean_le hν e i hi g

/--
[expect_cond_eq_of_indep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma expect_cond_eq_of_indep_eq
  [Fintype E]
  [DecidableEq E]
  {e : E}
  {b : Bool}
  {k : ConfigSpace E → ℝ}
-- given
  (hν : IsProbWeight ν)
  (hk : ∀ ω, k (flipAt e ω) = k ω) :
-- imply
  expect (Function.update ν e (pt b)) k = expect ν k := by
-- proof
  apply StatMech.OSSS.expect_cond_eq_of_indep hν e b k hk

/--
[expect_condMean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma expect_condMean_eq
  [Fintype E]
  [DecidableEq E]
  {e : E}
  {g : ConfigSpace E → ℝ}
-- given
  (hν : IsProbWeight ν) :
-- imply
  expect ν (condMean ν e g) = expect ν g := by
-- proof
  apply StatMech.OSSS.expect_condMean hν e g

/--
[diff_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma diff_flip_eq
  [Fintype E]
  [DecidableEq E]
  {e : E}
  {g : ConfigSpace E → ℝ}
  {ω : ConfigSpace E} :
-- imply
  (g (setOpen e (flipAt e ω)) - g (setClosed e (flipAt e ω))) = g (setOpen e ω) - g (setClosed e ω) := by
-- proof
  apply StatMech.OSSS.diff_flip e g ω

/--
[expect_fluct_condT](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma expect_fluct_condT_eq
  [Fintype E]
  [DecidableEq E]
  {e : E}
  {F g : ConfigSpace E → ℝ}
-- given
  (hν : IsProbWeight ν) :
-- imply
  expect (Function.update ν e (pt true)) (fun ω => F ω * (g ω - condMean ν e g ω)) = ν e false * expect ν (fun ω => F (setOpen e ω) * (g (setOpen e ω) - g (setClosed e ω))) := by
-- proof
  apply StatMech.OSSS.expect_fluct_condT hν e F g

/--
[expect_fluct_condF](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma expect_fluct_condF_eq
  [Fintype E]
  [DecidableEq E]
  {e : E}
  {F g : ConfigSpace E → ℝ}
-- given
  (hν : IsProbWeight ν) :
-- imply
  expect (Function.update ν e (pt false)) (fun ω => F ω * (g ω - condMean ν e g ω)) = (- ν e true) * expect ν (fun ω => F (setClosed e ω) * (g (setOpen e ω) - g (setClosed e ω))) := by
-- proof
  apply StatMech.OSSS.expect_fluct_condF hν e F g

/--
[expect_fluctuation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma expect_fluctuation_eq
  [Fintype E]
  [DecidableEq E]
  {e : E}
  {F g : ConfigSpace E → ℝ}
-- given
  (hν : IsProbWeight ν) :
-- imply
  expect ν (fun ω => F ω * (g ω - condMean ν e g ω)) = ν e true * ν e false * expect ν (fun ω => (F (setOpen e ω) - F (setClosed e ω)) * (g (setOpen e ω) - g (setClosed e ω))) := by
-- proof
  apply StatMech.OSSS.expect_fluctuation hν e F g

/--
[expect_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma expect_zero_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ} :
-- imply
  expect ν (fun _ => 0) = 0 := by
-- proof
  apply StatMech.OSSS.expect_zero ν

/--
[infl_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma infl_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {g : ConfigSpace E → ℝ}
  {i : E}
-- given
  (hν : IsProbWeight ν) :
-- imply
  0 ≤ infl ν g i := by
-- proof
  apply StatMech.OSSS.infl_nonneg hν g i

/--
[claimA](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma claimA_eq
  [Fintype E]
  [DecidableEq E]
  {e : E}
  {F g : ConfigSpace E → ℝ}
-- given
  (hν : IsProbWeight ν)
  (hF : ∀ ω, |F (setOpen e ω) - F (setClosed e ω)| ≤ 1) :
-- imply
  cov ν F (fun ω => g ω - condMean ν e g ω) ≤ infl ν g e := by
-- proof
  apply StatMech.OSSS.claimA hν e F g hF

/--
[cov_add_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma cov_add_right_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
-- given
  (F g h : ConfigSpace E → ℝ) :
-- imply
  cov ν F (fun ω => g ω + h ω) = cov ν F g + cov ν F h := by
-- proof
  apply StatMech.OSSS.cov_add_right ν F g h

/--
[cov_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma cov_decomp_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {e : E}
  {F g : ConfigSpace E → ℝ} :
-- imply
  cov ν F g = cov ν F (fun ω => g ω - condMean ν e g ω) + cov ν F (condMean ν e g) := by
-- proof
  apply StatMech.OSSS.cov_decomp ν e F g

/--
[evalR_node_of_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma evalR_node_of_eq_eq
  [Fintype E]
  [DecidableEq E]
  {e : E}
  {t f : DecisionTree E}
  {ω : ConfigSpace E}
  {b : Bool}
-- given
  (h : ω e = b) :
-- imply
  (DecisionTree.node e t f).evalR ω = (if b then t else f).evalR ω := by
-- proof
  apply StatMech.OSSS.evalR_node_of_eq e t f ω b h

/--
[expect_evalR_node_cond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma expect_evalR_node_cond_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {e : E}
  {b : Bool}
  {t f : DecisionTree E}
-- given
  (h : ConfigSpace E → ℝ) :
-- imply
  expect (Function.update ν e (pt b)) (fun ω => (DecisionTree.node e t f).evalR ω * h ω) = expect (Function.update ν e (pt b)) (fun ω => (if b then t else f).evalR ω * h ω) := by
-- proof
  apply StatMech.OSSS.expect_evalR_node_cond ν e b t f h

/--
[claimB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma claimB_eq
  [Fintype E]
  [DecidableEq E]
  {e : E}
  {t f : DecisionTree E}
  {G : ConfigSpace E → ℝ}
-- given
  (hν : IsProbWeight ν)
  (hG : ∀ ω, G (flipAt e ω) = G ω) :
-- imply
  cov ν (DecisionTree.node e t f).evalR G = ν e true * cov (Function.update ν e (pt true)) t.evalR G + ν e false * cov (Function.update ν e (pt false)) f.evalR G := by
-- proof
  apply StatMech.OSSS.claimB hν e t f G hG

/--
[condMean_flipAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma condMean_flipAt_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {e : E}
  {g : ConfigSpace E → ℝ}
  {ω : ConfigSpace E} :
-- imply
  condMean ν e g (flipAt e ω) = condMean ν e g ω := by
-- proof
  apply StatMech.OSSS.condMean_flipAt ν e g ω

/--
[infl_condMean_cond_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma infl_condMean_cond_eq_eq
  [Fintype E]
  [DecidableEq E]
  {e i : E}
  {b : Bool}
  {g : ConfigSpace E → ℝ}
-- given
  (hν : IsProbWeight ν)
  (hi : i ≠ e) :
-- imply
  infl (Function.update ν e (pt b)) (condMean ν e g) i = infl ν (condMean ν e g) i := by
-- proof
  apply StatMech.OSSS.infl_condMean_cond_eq hν e i hi b g

/--
[expect_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma expect_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {g : ConfigSpace E → ℝ}
-- given
  (hν : IsProbWeight ν)
  (hg : ∀ ω, 0 ≤ g ω) :
-- imply
  0 ≤ expect ν g := by
-- proof
  apply StatMech.OSSS.expect_nonneg hν hg

/--
[reveal_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma reveal_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {T : DecisionTree E}
  {i : E}
-- given
  (hν : IsProbWeight ν) :
-- imply
  0 ≤ reveal ν T i := by
-- proof
  apply StatMech.OSSS.reveal_nonneg hν T i

/--
[isProbWeight_cond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma isProbWeight_cond_eq
  [Fintype E]
  [DecidableEq E]
  {e : E}
  {b : Bool}
-- given
  (hν : IsProbWeight ν) :
-- imply
  IsProbWeight (Function.update ν e (pt b)) := by
-- proof
  apply StatMech.OSSS.isProbWeight_cond hν e b

/--
[infl_condMean_self'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma infl_condMean_self'_eq
  [Fintype E]
  [DecidableEq E]
  {μ ν : E → Bool → ℝ}
  {e : E}
  {g : ConfigSpace E → ℝ} :
-- imply
  infl μ (condMean ν e g) e = 0 := by
-- proof
  apply StatMech.OSSS.infl_condMean_self' μ ν e g

/--
[recombine_term](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma recombine_term_eq
  [Fintype E]
  [DecidableEq E]
  {e i : E}
  {t f : DecisionTree E}
  {g : ConfigSpace E → ℝ}
-- given
  (hν : IsProbWeight ν) :
-- imply
  ν e true * (reveal (Function.update ν e (pt true)) t i * infl (Function.update ν e (pt true)) (condMean ν e g) i) + ν e false * (reveal (Function.update ν e (pt false)) f i * infl (Function.update ν e (pt false)) (condMean ν e g) i) = reveal ν (.node e t f) i * infl ν (condMean ν e g) i := by
-- proof
  apply StatMech.OSSS.recombine_term hν e i t f g

/--
[recombine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma recombine_eq
  [Fintype E]
  [DecidableEq E]
  {e : E}
  {t f : DecisionTree E}
  {g : ConfigSpace E → ℝ}
-- given
  (hν : IsProbWeight ν) :
-- imply
  ν e true * (∑ i, reveal (Function.update ν e (pt true)) t i * infl (Function.update ν e (pt true)) (condMean ν e g) i) + ν e false * (∑ i, reveal (Function.update ν e (pt false)) f i * infl (Function.update ν e (pt false)) (condMean ν e g) i) = ∑ i, reveal ν (.node e t f) i * infl ν (condMean ν e g) i := by
-- proof
  apply StatMech.OSSS.recombine hν e t f g

/--
[cov_condMean_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma cov_condMean_bound_eq
  [Fintype E]
  [DecidableEq E]
  {e : E}
  {t f : DecisionTree E}
  {g : ConfigSpace E → ℝ}
-- given
  (hν : IsProbWeight ν)
  (IHt : ∀ μ, IsProbWeight μ → ∀ h : ConfigSpace E → ℝ, cov μ t.evalR h ≤ ∑ i, reveal μ t i * infl μ h i)
  (IHf : ∀ μ, IsProbWeight μ → ∀ h : ConfigSpace E → ℝ, cov μ f.evalR h ≤ ∑ i, reveal μ f i * infl μ h i) :
-- imply
  cov ν (DecisionTree.node e t f).evalR (condMean ν e g) ≤ ∑ i, reveal ν (.node e t f) i * infl ν (condMean ν e g) i := by
-- proof
  apply StatMech.OSSS.cov_condMean_bound hν e t f g IHt IHf

/--
[reveal_infl_condMean_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma reveal_infl_condMean_le_eq
  [Fintype E]
  [DecidableEq E]
  {e i : E}
  {t f : DecisionTree E}
  {g : ConfigSpace E → ℝ}
-- given
  (hν : IsProbWeight ν) :
-- imply
  reveal ν (.node e t f) i * infl ν (condMean ν e g) i ≤ reveal ν (.node e t f) i * infl ν g i := by
-- proof
  apply StatMech.OSSS.reveal_infl_condMean_le hν e i t f g

/--
[osss_cov](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma osss_cov_eq
  [Fintype E]
  [DecidableEq E]
  {T : DecisionTree E} :
-- imply
  ∀ ν, IsProbWeight ν → ∀ g : ConfigSpace E → ℝ, cov ν T.evalR g ≤ ∑ i, reveal ν T i * infl ν g i := by
-- proof
  apply StatMech.OSSS.osss_cov T

/--
[osss_var](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma osss_var_eq
  [Fintype E]
  [DecidableEq E]
  {T : DecisionTree E}
-- given
  (hν : IsProbWeight ν) :
-- imply
  var ν T.evalR ≤ ∑ i, reveal ν T i * infl ν T.evalR i := by
-- proof
  apply StatMech.OSSS.osss_var hν T

/--
[osss](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma osss_eq
  [Fintype E]
  [DecidableEq E]
  {T : DecisionTree E}
  {g : ConfigSpace E → ℝ}
-- given
  (hν : IsProbWeight ν) :
-- imply
  cov ν T.evalR g ≤ ∑ i, reveal ν T i * infl ν g i := by
-- proof
  apply StatMech.OSSS.osss hν T g

/--
[bernoulliWeight_isProbWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma bernoulliWeight_isProbWeight_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1) :
-- imply
  IsProbWeight (E := E) (bernoulliWeight p) := by
-- proof
  apply StatMech.OSSS.bernoulliWeight_isProbWeight hp0 hp1

/--
[osss_bernoulli](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma osss_bernoulli_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {T : DecisionTree E}
  {g : ConfigSpace E → ℝ}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1) :
-- imply
  cov (bernoulliWeight p) T.evalR g ≤ ∑ i, reveal (bernoulliWeight p) T i * infl (bernoulliWeight p) g i := by
-- proof
  apply StatMech.OSSS.osss_bernoulli hp0 hp1 T g

/--
[abs_indicator_diff_eq_pivotal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma abs_indicator_diff_eq_pivotal_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {e : E}
  {ω : ConfigSpace E} :
-- imply
  |A.indicator (fun _ => (1:ℝ)) (setOpen e ω) - A.indicator (fun _ => (1:ℝ)) (setClosed e ω)| = {ω | IsPivotal e A ω}.indicator (fun _ => (1:ℝ)) ω := by
-- proof
  apply StatMech.OSSS.abs_indicator_diff_eq_pivotal A e ω

/--
[infl_indicator_eq_pivotal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean)
-/
@[path]
private lemma infl_indicator_eq_pivotal_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {A : Set (ConfigSpace E)}
  {e : E} :
-- imply
  infl ν (A.indicator (fun _ => (1:ℝ))) e = expect ν ({ω | IsPivotal e A ω}.indicator (fun _ => (1:ℝ))) := by
-- proof
  apply StatMech.OSSS.infl_indicator_eq_pivotal ν A e


-- created on 2026-10-23
