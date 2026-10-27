import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Probability.CoupledTensorizeProve.Part2
open Finset Real Set StatMech StatMech.Probability


/--
[ctp_cfg_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/CoupledTensorizeProve.lean)
-/
@[path]
private lemma ctp_cfg_zero_eq
  {a b : Bool} :
-- imply
  ctp_cfg a b 0 = a := by
-- proof
  apply StatMech.Probability.ctp_cfg_zero a b

/--
[ctp_cfg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/CoupledTensorizeProve.lean)
-/
@[path]
private lemma ctp_cfg_one_eq
  {a b : Bool} :
-- imply
  ctp_cfg a b 1 = b := by
-- proof
  apply StatMech.Probability.ctp_cfg_one a b

/--
[ctp_sum_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/CoupledTensorizeProve.lean)
-/
@[path]
private lemma ctp_sum_fin2_eq
  {g : ConfigSpace (Fin 2) → ℝ} :
-- imply
  ∑ ω : ConfigSpace (Fin 2), g ω = g (ctp_cfg false false) + g (ctp_cfg false true) + g (ctp_cfg true false) + g (ctp_cfg true true) := by
-- proof
  apply StatMech.Probability.ctp_sum_fin2 g

/--
[ctp_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/CoupledTensorizeProve.lean)
-/
@[path]
private lemma ctp_weight_eq
  {p : ℝ}
  {a b : Bool} :
-- imply
  OSSS.weight (OSSS.bernoulliWeight p) (ctp_cfg a b) = (if a then p else 1 - p) * (if b then p else 1 - p) := by
-- proof
  apply StatMech.Probability.ctp_weight p a b

/--
[ctp_expect_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/CoupledTensorizeProve.lean)
-/
@[path]
private lemma ctp_expect_fin2_eq
  {p : ℝ}
  {g : ConfigSpace (Fin 2) → ℝ} :
-- imply
  OSSS.expect (OSSS.bernoulliWeight p) g = (1 - p) * (1 - p) * g (ctp_cfg false false) + (1 - p) * p * g (ctp_cfg false true) + p * (1 - p) * g (ctp_cfg true false) + p * p * g (ctp_cfg true true) := by
-- proof
  apply StatMech.Probability.ctp_expect_fin2 p g

/--
[ctp_f_ff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/CoupledTensorizeProve.lean)
-/
@[path]
private lemma ctp_f_ff_eq :
-- imply
  ctp_f (ctp_cfg false false) = 0 := by
-- proof
  apply StatMech.Probability.ctp_f_ff

/--
[ctp_f_ft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/CoupledTensorizeProve.lean)
-/
@[path]
private lemma ctp_f_ft_eq :
-- imply
  ctp_f (ctp_cfg false true) = 1 := by
-- proof
  apply StatMech.Probability.ctp_f_ft

/--
[ctp_f_tf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/CoupledTensorizeProve.lean)
-/
@[path]
private lemma ctp_f_tf_eq :
-- imply
  ctp_f (ctp_cfg true false) = 1 := by
-- proof
  apply StatMech.Probability.ctp_f_tf

/--
[ctp_f_tt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/CoupledTensorizeProve.lean)
-/
@[path]
private lemma ctp_f_tt_eq :
-- imply
  ctp_f (ctp_cfg true true) = 1 := by
-- proof
  apply StatMech.Probability.ctp_f_tt

/--
[ctp_psi_eval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/CoupledTensorizeProve.lean)
-/
@[path]
private lemma ctp_psi_eval_eq
  {p : ℝ}
  {b : Bool} :
-- imply
  ptn_psi p b = ((if b then (1:ℝ) else 0) - p) / ptn_sigma p := by
-- proof
  apply StatMech.Probability.ctp_psi_eval p b

/--
[ctp_pchar_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/CoupledTensorizeProve.lean)
-/
@[path]
private lemma ctp_pchar_zero_eq
  {p : ℝ}
  {ω : ConfigSpace (Fin 2)} :
-- imply
  ptn_pchar p {0} ω = ptn_psi p (ω 0) := by
-- proof
  apply StatMech.Probability.ctp_pchar_zero p ω

/--
[ctp_pchar_zeroone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/CoupledTensorizeProve.lean)
-/
@[path]
private lemma ctp_pchar_zeroone_eq
  {p : ℝ}
  {ω : ConfigSpace (Fin 2)} :
-- imply
  ptn_pchar p ({0, 1} : Finset (Fin 2)) ω = ptn_psi p (ω 0) * ptn_psi p (ω 1) := by
-- proof
  apply StatMech.Probability.ctp_pchar_zeroone p ω

/--
[ctp_coeff_zero_sq_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/CoupledTensorizeProve.lean)
-/
@[path]
private lemma ctp_coeff_zero_sq_div_eq :
-- imply
  (ptn_coeff (9/10 : ℝ) ctp_f {0} / ptn_sigma (9/10)) ^ 2 = 1 / 100 := by
-- proof
  apply StatMech.Probability.ctp_coeff_zero_sq_div

/--
[ctp_coeff_zeroone_sq_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/CoupledTensorizeProve.lean)
-/
@[path]
private lemma ctp_coeff_zeroone_sq_div_eq :
-- imply
  (ptn_coeff (9/10 : ℝ) ctp_f ({0,1} : Finset (Fin 2)) / ptn_sigma (9/10)) ^ 2 = 9 / 100 := by
-- proof
  apply StatMech.Probability.ctp_coeff_zeroone_sq_div

/--
[ctp_OR_infl0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/CoupledTensorizeProve.lean)
-/
@[path]
private lemma ctp_OR_infl0_eq :
-- imply
  OSSS.infl (OSSS.bernoulliWeight (9/10 : ℝ)) ctp_f 0 = 1 / 10 := by
-- proof
  apply StatMech.Probability.ctp_OR_infl0

/--
[ctp_filter_mem0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/CoupledTensorizeProve.lean)
-/
@[path]
private lemma ctp_filter_mem0_eq :
-- imply
  (univ.filter (fun S : Finset (Fin 2) => (0 : Fin 2) ∈ S)) = {({0} : Finset (Fin 2)), ({0, 1} : Finset (Fin 2))} := by
-- proof
  apply StatMech.Probability.ctp_filter_mem0

/--
[ctp_OR_lhs_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/CoupledTensorizeProve.lean)
-/
@[path]
private lemma ctp_OR_lhs_eq_eq :
-- imply
  (∑ S ∈ univ.filter (fun S : Finset (Fin 2) => (0 : Fin 2) ∈ S), (1 - (1/2 : ℝ)) ^ (S.erase 0).card * (ptn_coeff (9/10 : ℝ) ctp_f S / ptn_sigma (9/10)) ^ 2) = 11 / 200 := by
-- proof
  apply StatMech.Probability.ctp_OR_lhs_eq

/--
[ctp_rhs_lt_lhs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/CoupledTensorizeProve.lean)
-/
@[path]
private lemma ctp_rhs_lt_lhs_eq :
-- imply
  ((1:ℝ) / 10) ^ ((4:ℝ) / 3) < 11 / 200 := by
-- proof
  apply StatMech.Probability.ctp_rhs_lt_lhs

/--
[ctp_perCoordHighNoise_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/CoupledTensorizeProve.lean)
-/
@[path]
private lemma ctp_perCoordHighNoise_false_eq
  {q : ℝ}
-- given
  (hq : (9 : ℝ) / 10 < q) :
-- imply
  ¬ mfp2_PerCoordHighNoise q := by
-- proof
  apply StatMech.Probability.ctp_perCoordHighNoise_false hq

/--
[ctp_engine_holds_at_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/CoupledTensorizeProve.lean)
-/
@[path]
private lemma ctp_engine_holds_at_witness_eq :
-- imply
  (∑ S ∈ univ.filter (fun S : Finset (Fin 2) => (0 : Fin 2) ∈ S), (Real.sqrt ((3/2 - 1) * 4 * (9/10) * (1 - 9/10)) ^ (S.erase 0).card) ^ 2 * (ptn_coeff (9/10 : ℝ) (fun ω => if ctp_OR ω then (1:ℝ) else 0) S / ptn_sigma (9/10)) ^ 2) ≤ (OSSS.infl (OSSS.bernoulliWeight (9/10 : ℝ)) (fun ω => if ctp_OR ω then (1:ℝ) else 0) 0) ^ (2 / (3/2 : ℝ)) := by
-- proof
  apply StatMech.Probability.ctp_engine_holds_at_witness

/--
[ctp_perCoordHighNoise_unsatisfiable_but_reduction_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/CoupledTensorizeProve.lean)
-/
@[path]
private lemma ctp_perCoordHighNoise_unsatisfiable_but_reduction_valid_eq
  {q : ℝ}
-- given
  (hq : (9 : ℝ) / 10 < q) :
-- imply
  (¬ mfp2_PerCoordHighNoise q) ∧ (mfp2_PerCoordHighNoise q → frh_openResidue q) := by
-- proof
  apply StatMech.Probability.ctp_perCoordHighNoise_unsatisfiable_but_reduction_valid hq

/--
[ctp_half_holds_but_window_fails](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/CoupledTensorizeProve.lean)
-/
@[path]
private lemma ctp_half_holds_but_window_fails_eq
  {q : ℝ}
-- given
  (hq : (9 : ℝ) / 10 < q) :
-- imply
  (∀ {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool) (u : ℝ), 0 < u → u < 1 → ∀ e : E, (∑ S ∈ univ.filter (fun S : Finset E => e ∈ S), (1 - u) ^ (S.erase e).card * (ptn_coeff (1/2 : ℝ) (fun ω => if φ ω then (1:ℝ) else 0) S / ptn_sigma (1/2)) ^ 2) ≤ (OSSS.infl (OSSS.bernoulliWeight (1/2 : ℝ)) (fun ω => if φ ω then (1:ℝ) else 0) e) ^ (2 / (2 - u))) ∧ ¬ mfp2_PerCoordHighNoise q := by
-- proof
  apply StatMech.Probability.ctp_half_holds_but_window_fails hq


-- created on 2026-10-23
