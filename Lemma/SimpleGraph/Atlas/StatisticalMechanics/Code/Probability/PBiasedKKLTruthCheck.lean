import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Probability.PBiasedKKLTruthCheck.Part2
open Finset Real Set StatMech StatMech.Probability


/--
[pbkt_OR_expect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedKKLTruthCheck.lean)
-/
@[path]
private lemma pbkt_OR_expect_eq
  {p : ℝ} :
-- imply
  OSSS.expect (OSSS.bernoulliWeight p) ctp_f = 1 - (1 - p) ^ 2 := by
-- proof
  apply StatMech.Probability.pbkt_OR_expect p

/--
[pbkt_OR_var](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedKKLTruthCheck.lean)
-/
@[path]
private lemma pbkt_OR_var_eq
  {p : ℝ} :
-- imply
  OSSS.var (OSSS.bernoulliWeight p) ctp_f = (1 - (1 - p) ^ 2) * (1 - p) ^ 2 := by
-- proof
  apply StatMech.Probability.pbkt_OR_var p

/--
[pbkt_OR_infl0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedKKLTruthCheck.lean)
-/
@[path]
private lemma pbkt_OR_infl0_eq
  {p : ℝ} :
-- imply
  OSSS.infl (OSSS.bernoulliWeight p) ctp_f 0 = 1 - p := by
-- proof
  apply StatMech.Probability.pbkt_OR_infl0 p

/--
[pbkt_OR_infl1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedKKLTruthCheck.lean)
-/
@[path]
private lemma pbkt_OR_infl1_eq
  {p : ℝ} :
-- imply
  OSSS.infl (OSSS.bernoulliWeight p) ctp_f 1 = 1 - p := by
-- proof
  apply StatMech.Probability.pbkt_OR_infl1 p

/--
[pbkt_OR_totalInfl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedKKLTruthCheck.lean)
-/
@[path]
private lemma pbkt_OR_totalInfl_eq
  {p : ℝ} :
-- imply
  totalInfl (OSSS.bernoulliWeight p) ctp_f = 2 * (1 - p) := by
-- proof
  apply StatMech.Probability.pbkt_OR_totalInfl p

/--
[pbkt_OR_maxInfl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedKKLTruthCheck.lean)
-/
@[path]
private lemma pbkt_OR_maxInfl_eq
  {p : ℝ} :
-- imply
  maxInfl (OSSS.bernoulliWeight p) ctp_f = 1 - p := by
-- proof
  apply StatMech.Probability.pbkt_OR_maxInfl p

/--
[pbkt_twoBit_atom_numeric](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedKKLTruthCheck.lean)
-/
@[path]
private lemma pbkt_twoBit_atom_numeric_eq
  {x : ℝ}
-- given
  (hx0 : 0 < x)
  (hx1 : x < 1) :
-- imply
  2 * ((1 - x ^ 2) * x ^ 2) * Real.log (1 / x) ≤ 2 * x := by
-- proof
  apply StatMech.Probability.pbkt_twoBit_atom_numeric hx0 hx1

/--
[pbkt_OR_kkl_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedKKLTruthCheck.lean)
-/
@[path]
private lemma pbkt_OR_kkl_two_eq
  {p : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  2 * OSSS.var (OSSS.bernoulliWeight p) ctp_f * Real.log (1 / maxInfl (OSSS.bernoulliWeight p) ctp_f) ≤ totalInfl (OSSS.bernoulliWeight p) ctp_f := by
-- proof
  apply StatMech.Probability.pbkt_OR_kkl_two hp0 hp1

/--
[pbkt_andF_ff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedKKLTruthCheck.lean)
-/
@[path]
private lemma pbkt_andF_ff_eq :
-- imply
  pbkt_andF (ctp_cfg false false) = 0 := by
-- proof
  apply StatMech.Probability.pbkt_andF_ff

/--
[pbkt_andF_ft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedKKLTruthCheck.lean)
-/
@[path]
private lemma pbkt_andF_ft_eq :
-- imply
  pbkt_andF (ctp_cfg false true) = 0 := by
-- proof
  apply StatMech.Probability.pbkt_andF_ft

/--
[pbkt_andF_tf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedKKLTruthCheck.lean)
-/
@[path]
private lemma pbkt_andF_tf_eq :
-- imply
  pbkt_andF (ctp_cfg true false) = 0 := by
-- proof
  apply StatMech.Probability.pbkt_andF_tf

/--
[pbkt_andF_tt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedKKLTruthCheck.lean)
-/
@[path]
private lemma pbkt_andF_tt_eq :
-- imply
  pbkt_andF (ctp_cfg true true) = 1 := by
-- proof
  apply StatMech.Probability.pbkt_andF_tt

/--
[pbkt_AND_expect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedKKLTruthCheck.lean)
-/
@[path]
private lemma pbkt_AND_expect_eq
  {p : ℝ} :
-- imply
  OSSS.expect (OSSS.bernoulliWeight p) pbkt_andF = p ^ 2 := by
-- proof
  apply StatMech.Probability.pbkt_AND_expect p

/--
[pbkt_AND_var](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedKKLTruthCheck.lean)
-/
@[path]
private lemma pbkt_AND_var_eq
  {p : ℝ} :
-- imply
  OSSS.var (OSSS.bernoulliWeight p) pbkt_andF = (1 - p ^ 2) * p ^ 2 := by
-- proof
  apply StatMech.Probability.pbkt_AND_var p

/--
[pbkt_AND_infl0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedKKLTruthCheck.lean)
-/
@[path]
private lemma pbkt_AND_infl0_eq
  {p : ℝ} :
-- imply
  OSSS.infl (OSSS.bernoulliWeight p) pbkt_andF 0 = p := by
-- proof
  apply StatMech.Probability.pbkt_AND_infl0 p

/--
[pbkt_AND_infl1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedKKLTruthCheck.lean)
-/
@[path]
private lemma pbkt_AND_infl1_eq
  {p : ℝ} :
-- imply
  OSSS.infl (OSSS.bernoulliWeight p) pbkt_andF 1 = p := by
-- proof
  apply StatMech.Probability.pbkt_AND_infl1 p

/--
[pbkt_AND_totalInfl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedKKLTruthCheck.lean)
-/
@[path]
private lemma pbkt_AND_totalInfl_eq
  {p : ℝ} :
-- imply
  totalInfl (OSSS.bernoulliWeight p) pbkt_andF = 2 * p := by
-- proof
  apply StatMech.Probability.pbkt_AND_totalInfl p

/--
[pbkt_AND_maxInfl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedKKLTruthCheck.lean)
-/
@[path]
private lemma pbkt_AND_maxInfl_eq
  {p : ℝ} :
-- imply
  maxInfl (OSSS.bernoulliWeight p) pbkt_andF = p := by
-- proof
  apply StatMech.Probability.pbkt_AND_maxInfl p

/--
[pbkt_AND_kkl_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedKKLTruthCheck.lean)
-/
@[path]
private lemma pbkt_AND_kkl_two_eq
  {p : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  2 * OSSS.var (OSSS.bernoulliWeight p) pbkt_andF * Real.log (1 / maxInfl (OSSS.bernoulliWeight p) pbkt_andF) ≤ totalInfl (OSSS.bernoulliWeight p) pbkt_andF := by
-- proof
  apply StatMech.Probability.pbkt_AND_kkl_two hp0 hp1

/--
[pbkt_dictator_kkl_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedKKLTruthCheck.lean)
-/
@[path]
private lemma pbkt_dictator_kkl_two_eq
  {p : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  2 * OSSS.var (OSSS.bernoulliWeight p) (fun ω : ConfigSpace (Fin 1) => if ω 0 then (1 : ℝ) else 0) * Real.log (1 / maxInfl (OSSS.bernoulliWeight p) (fun ω : ConfigSpace (Fin 1) => if ω 0 then (1 : ℝ) else 0)) ≤ totalInfl (OSSS.bernoulliWeight p) (fun ω : ConfigSpace (Fin 1) => if ω 0 then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.pbkt_dictator_kkl_two hp0 hp1


-- created on 2026-10-23
