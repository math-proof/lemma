import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.fkc_rqvanhove.Part4
open SimpleGraph Filter Topology Set StatMech StatMech.Walls


/--
[fkc_edgeFreeEnergy_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fkc_rqvanhove.lean)
-/
@[path]
private lemma fkc_edgeFreeEnergy_eq_eq
  {d : ℕ}
  {s q : ℝ}
  {n : ℕ} :
-- imply
  fkc_edgeFreeEnergy d s q n = -fkc_f d s q n + Real.log (1 + Real.exp s) := by
-- proof
  apply StatMech.Walls.fkc_edgeFreeEnergy_eq d s q n

/--
[fkc_u_q2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fkc_rqvanhove.lean)
-/
@[path]
private lemma fkc_u_q2_eq
  {d : ℕ}
  {s : ℝ}
  {n : ℕ} :
-- imply
  fkc_u d s 2 n = ecz_u d s n := by
-- proof
  apply StatMech.Walls.fkc_u_q2 d s n

/--
[fkc_box_neglog_doubling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fkc_rqvanhove.lean)
-/
@[path]
private lemma fkc_box_neglog_doubling_eq
  {d K : ℕ}
  {s q : ℝ}
-- given
  (hq : 1 ≤ q) :
-- imply
  fkc_u d s q (2 * K + 1) ≤ (2 : ℝ) ^ d * fkc_u d s q K + ((2 * d * (qp_Jset d K).card + (2 ^ d + 1) * (2 * d * (qp_Jset d K).card) : ℕ) : ℝ) * (-Real.log (1 - fsc_logistic s)) := by
-- proof
  apply StatMech.Walls.fkc_box_neglog_doubling d K s q hq

/--
[fkc_box_vanHove_subadd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fkc_rqvanhove.lean)
-/
@[path]
private lemma fkc_box_vanHove_subadd_eq
  {d m n : ℕ}
  {s q : ℝ}
-- given
  (hq : 1 ≤ q) :
-- imply
  fkc_u d s q n ≤ ((ecz_T m n) ^ d : ℝ) * fkc_u d s q m + (((boxGraph d n).edgeFinset.card : ℝ) - ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ)) * (-Real.log (1 - fsc_logistic s)) := by
-- proof
  apply StatMech.Walls.fkc_box_vanHove_subadd d m n s q hq

/--
[fkc_perEdge_vanHove](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fkc_rqvanhove.lean)
-/
@[path]
private lemma fkc_perEdge_vanHove_eq
  {d m n : ℕ}
  {s q : ℝ}
-- given
  (hq : 1 ≤ q)
  (hEn : 0 < (boxGraph d n).edgeFinset.card)
  (hEm : 0 < (boxGraph d m).edgeFinset.card) :
-- imply
  fkc_f d s q n ≤ (((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ) / ((boxGraph d n).edgeFinset.card : ℝ)) * fkc_f d s q m + (1 - ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ) / ((boxGraph d n).edgeFinset.card : ℝ)) * (-Real.log (1 - fsc_logistic s)) := by
-- proof
  apply StatMech.Walls.fkc_perEdge_vanHove d m n s q hq hEn hEm

/--
[fkc_additiveDoublingBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fkc_rqvanhove.lean)
-/
@[path]
private lemma fkc_additiveDoublingBound_eq
  {d : ℕ}
  {s q : ℝ}
-- given
  (hd : 1 ≤ d)
  (hq : 1 ≤ q) :
-- imply
  fkc_AdditiveDoublingBound d s q := by
-- proof
  apply StatMech.Walls.fkc_additiveDoublingBound d hd s q hq

/--
[fkc_dyadic_f_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fkc_rqvanhove.lean)
-/
@[path]
private lemma fkc_dyadic_f_tendsto_eq
  {d : ℕ}
  {s q : ℝ}
-- given
  (hd : 1 ≤ d)
  (hq : 1 ≤ q) :
-- imply
  ∃ L : ℝ, Tendsto (fun j => fkc_f d s q (agl_K j)) atTop (nhds L) := by
-- proof
  apply StatMech.Walls.fkc_dyadic_f_tendsto d hd s q hq

/--
[fkc_f_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fkc_rqvanhove.lean)
-/
@[path]
private lemma fkc_f_lower_eq
  {d : ℕ}
  {s q : ℝ}
  {n : ℕ}
  {L : ℝ}
-- given
  (hd : 1 ≤ d)
  (hq : 1 ≤ q)
  (hn : 1 ≤ n)
  (hL : Tendsto (fun j => fkc_f d s q (agl_K j)) atTop (nhds L)) :
-- imply
  ((2 * (n : ℝ) + 1) / (2 * n)) * L - (-Real.log (1 - fsc_logistic s)) / (2 * n) ≤ fkc_f d s q n := by
-- proof
  apply StatMech.Walls.fkc_f_lower d hd s q hq n hn L hL

/--
[fkc_g_dyadic_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fkc_rqvanhove.lean)
-/
@[path]
private lemma fkc_g_dyadic_tendsto_eq
  {d : ℕ}
  {s q L : ℝ}
-- given
  (hL : Tendsto (fun j => fkc_f d s q (agl_K j)) atTop (nhds L)) :
-- imply
  Tendsto (fun j => fkc_g d s q (agl_K j)) atTop (nhds L) := by
-- proof
  apply StatMech.Walls.fkc_g_dyadic_tendsto d s q L hL

/--
[fkc_upperSeq_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fkc_rqvanhove.lean)
-/
@[path]
private lemma fkc_upperSeq_tendsto_eq
  {d : ℕ}
  {s q : ℝ}
  {m : ℕ}
-- given
  (hd : 1 ≤ d)
  (hm : 1 ≤ m) :
-- imply
  Tendsto (fun n => (((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ) / ((boxGraph d n).edgeFinset.card : ℝ)) * fkc_f d s q m + (1 - ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ) / ((boxGraph d n).edgeFinset.card : ℝ)) * (-Real.log (1 - fsc_logistic s))) atTop (nhds (fkc_g d s q m)) := by
-- proof
  apply StatMech.Walls.fkc_upperSeq_tendsto d hd s q m hm

/--
[fkc_perEdgeDensityConverges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fkc_rqvanhove.lean)
-/
@[path]
private lemma fkc_perEdgeDensityConverges_eq
  {d : ℕ}
  {s q : ℝ}
-- given
  (hd : 1 ≤ d)
  (hq : 1 ≤ q) :
-- imply
  fkc_PerEdgeDensityConverges d s q := by
-- proof
  apply StatMech.Walls.fkc_perEdgeDensityConverges d hd s q hq


-- created on 2026-10-23
