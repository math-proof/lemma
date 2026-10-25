import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Probability.SummedBKKKLClose
open Finset Real Set intervalIntegral MeasureTheory StatMech StatMech.Probability


/--
[sbk_coeff0_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/SummedBKKKLClose.lean)
-/
@[path]
private lemma sbk_coeff0_sq_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  (ptn_coeff (9/10 : ℝ) ctp_f {0}) ^ 2 = 9 / 10000 := by
-- proof
  apply StatMech.Probability.sbk_coeff0_sq

/--
[sbk_coeff1_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/SummedBKKKLClose.lean)
-/
@[path]
private lemma sbk_coeff1_sq_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  (ptn_coeff (9/10 : ℝ) ctp_f {1}) ^ 2 = 9 / 10000 := by
-- proof
  apply StatMech.Probability.sbk_coeff1_sq

/--
[sbk_coeff01_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/SummedBKKKLClose.lean)
-/
@[path]
private lemma sbk_coeff01_sq_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  (ptn_coeff (9/10 : ℝ) ctp_f ({0,1}:Finset (Fin 2))) ^ 2 = 81 / 10000 := by
-- proof
  apply StatMech.Probability.sbk_coeff01_sq

/--
[sbk_OR_infl1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/SummedBKKKLClose.lean)
-/
@[path]
private lemma sbk_OR_infl1_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  OSSS.infl (OSSS.bernoulliWeight (9/10 : ℝ)) ctp_f 1 = 1 / 10 := by
-- proof
  apply StatMech.Probability.sbk_OR_infl1

/--
[sbk_OR_totalInfl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/SummedBKKKLClose.lean)
-/
@[path]
private lemma sbk_OR_totalInfl_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  totalInfl (OSSS.bernoulliWeight (9/10 : ℝ)) ctp_f = 1/5 := by
-- proof
  apply StatMech.Probability.sbk_OR_totalInfl

/--
[sbk_OR_maxInfl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/SummedBKKKLClose.lean)
-/
@[path]
private lemma sbk_OR_maxInfl_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  maxInfl (OSSS.bernoulliWeight (9/10 : ℝ)) ctp_f = 1/10 := by
-- proof
  apply StatMech.Probability.sbk_OR_maxInfl

/--
[sbk_univ_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/SummedBKKKLClose.lean)
-/
@[path]
private lemma sbk_univ_fin2_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0,1}} := by
-- proof
  apply StatMech.Probability.sbk_univ_fin2

/--
[sbk_OR_summed_lhs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/SummedBKKKLClose.lean)
-/
@[path]
private lemma sbk_OR_summed_lhs_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  (∑ S : Finset (Fin 2), 4 * (S.card : ℝ) * (1 - (1/2:ℝ)) ^ (S.card - 1) * (ptn_coeff (9/10:ℝ) ctp_f S) ^ 2) = 99/2500 := by
-- proof
  apply StatMech.Probability.sbk_OR_summed_lhs

/--
[sbk_numeric](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/SummedBKKKLClose.lean)
-/
@[path]
private lemma sbk_numeric_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  (99:ℝ)/500 ≤ ((1:ℝ)/10) ^ ((1:ℝ)/3) := by
-- proof
  apply StatMech.Probability.sbk_numeric

/--
[sbk_summed_holds_at_OR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/SummedBKKKLClose.lean)
-/
@[path]
private lemma sbk_summed_holds_at_OR_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  (∑ S : Finset (Fin 2), 4 * (S.card : ℝ) * (1 - (1/2:ℝ)) ^ (S.card - 1) * (ptn_coeff (9/10:ℝ) ctp_f S) ^ 2) ≤ (maxInfl (OSSS.bernoulliWeight (9/10:ℝ)) ctp_f) ^ ((1/2:ℝ) / (2 - 1/2)) * totalInfl (OSSS.bernoulliWeight (9/10:ℝ)) ctp_f := by
-- proof
  apply StatMech.Probability.sbk_summed_holds_at_OR

/--
[sbk_numeric_master_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/SummedBKKKLClose.lean)
-/
@[path]
private lemma sbk_numeric_master_false_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  ((1 : ℝ) / 10) ^ ((1 : ℝ) / 3) * (9 / 125) < 99 / 2500 := by
-- proof
  apply StatMech.Probability.sbk_numeric_master_false

/--
[sbk_pBiasedMaster_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/SummedBKKKLClose.lean)
-/
@[path]
private lemma sbk_pBiasedMaster_false_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
-- given
  (hq : (9 : ℝ) / 10 < q) :
-- imply
  ¬ pro_PBiasedMaster q := by
-- proof
  apply StatMech.Probability.sbk_pBiasedMaster_false hq

/--
[sbk_lowDegreeMasterResidue_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/SummedBKKKLClose.lean)
-/
@[path]
private lemma sbk_lowDegreeMasterResidue_false_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
-- given
  (hq : (9 : ℝ) / 10 < q) :
-- imply
  ¬ bkt_lowDegreeMasterResidue q := by
-- proof
  apply StatMech.Probability.sbk_lowDegreeMasterResidue_false hq

/--
[sbk_engine_integral_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/SummedBKKKLClose.lean)
-/
@[path]
private lemma sbk_engine_integral_eq_eq
  [Fintype ι]
  [DecidableEq ι]
  {n : ℕ}
  {s : ℝ} :
-- imply
  (∫ v in (1 - s)..(1:ℝ), ((n : ℝ) + 1) * (1 - v) ^ n) = s ^ (n + 1) := by
-- proof
  apply StatMech.Probability.sbk_engine_integral_eq n

/--
[sbk_engine_integral_damped](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/SummedBKKKLClose.lean)
-/
@[path]
private lemma sbk_engine_integral_damped_eq
  [Fintype ι]
  [DecidableEq ι]
  {s : ℝ}
  {d : ℕ}
-- given
  (hs0 : 0 < s)
  (hs1 : s < 1)
  (hd : 1 ≤ d) :
-- imply
  (∫ v in (1 - s)..(1:ℝ), (d : ℝ) * (1 - v) ^ (d - 1)) < 1 := by
-- proof
  apply StatMech.Probability.sbk_engine_integral_damped hs0 hs1 hd

/--
[sbk_openResidue_of_lowDegree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/SummedBKKKLClose.lean)
-/
@[path]
private lemma sbk_openResidue_of_lowDegree_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : bkt_lowDegreeMasterResidue q} :
-- imply
  frh_openResidue q := by
-- proof
  apply StatMech.Probability.sbk_openResidue_of_lowDegree H

/--
[sbk_kesten_of_lowDegree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/SummedBKKKLClose.lean)
-/
@[path]
private lemma sbk_kesten_of_lowDegree_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : bkt_lowDegreeMasterResidue q}
  {p : ℝ}
-- given
  (hp : p ∈ Set.Ioo (1 / 2 : ℝ) q)
  (hp1 : p < 1) :
-- imply
  KKLHypercontractive p 2 := by
-- proof
  apply StatMech.Probability.sbk_kesten_of_lowDegree H hp hp1

/--
[sbk_summed_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/SummedBKKKLClose.lean)
-/
@[path]
private lemma sbk_summed_half_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {φ : ConfigSpace ι → Bool}
  {u : ℝ}
-- given
  (hu0 : 0 < u)
  (hu1 : u < 1) :
-- imply
  (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * (ptn_coeff (1 / 2 : ℝ) (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) ≤ (maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u)) * totalInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.sbk_summed_half φ hu0 hu1

/--
[sbk_weightGap_vanishes_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/SummedBKKKLClose.lean)
-/
@[path]
private lemma sbk_weightGap_vanishes_half_eq
  [Fintype ι]
  [DecidableEq ι]
  {u : ℝ}
  {d : ℕ} :
-- imply
  (1 - u) ^ (d - 1) - ((1 - u) * (4 * (1/2:ℝ) * (1 - 1/2))) ^ (d - 1) = 0 := by
-- proof
  apply StatMech.Probability.sbk_weightGap_vanishes_half u d

/--
[sbk_summed_survives_percoord_fails](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/SummedBKKKLClose.lean)
-/
@[path]
private lemma sbk_summed_survives_percoord_fails_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
-- given
  (hq : (9 : ℝ) / 10 < q) :
-- imply
  (¬ mfp2_PerCoordHighNoise q) ∧ (∑ S : Finset (Fin 2), 4 * (S.card : ℝ) * (1 - (1/2:ℝ)) ^ (S.card - 1) * (ptn_coeff (9/10:ℝ) ctp_f S) ^ 2) ≤ (maxInfl (OSSS.bernoulliWeight (9/10:ℝ)) ctp_f) ^ ((1/2:ℝ) / (2 - 1/2)) * totalInfl (OSSS.bernoulliWeight (9/10:ℝ)) ctp_f ∧ (bkt_lowDegreeMasterResidue q → frh_openResidue q) := by
-- proof
  apply StatMech.Probability.sbk_summed_survives_percoord_fails hq


-- created on 2026-10-23
