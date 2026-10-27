import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.fc_core.Part8
open SimpleGraph Filter Topology Set StatMech StatMech.Walls


/--
[fc_fkZEdge_le_qpow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_core.lean)
-/
@[path]
private lemma fc_fkZEdge_le_qpow_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
-- given
  (hp : 0 ≤ p)
  (hp1 : p ≤ 1)
  (hq : 1 ≤ q) :
-- imply
  ecz_fkZEdge G p q ≤ (2 : ℝ) ^ G.edgeFinset.card * q ^ Fintype.card V := by
-- proof
  apply StatMech.Walls.fc_fkZEdge_le_qpow G hp hp1 hq

/--
[fc_u_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_core.lean)
-/
@[path]
private lemma fc_u_two_eq
  {d : ℕ}
  {t : ℝ}
  {n : ℕ} :
-- imply
  fc_u d 2 t n = ecz_u d t n := by
-- proof
  apply StatMech.Walls.fc_u_two t n

/--
[fc_edgeFE_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_core.lean)
-/
@[path]
private lemma fc_edgeFE_eq_eq
  {d : ℕ}
  {q : ℝ}
  {t : ℝ}
  {n : ℕ} :
-- imply
  fc_edgeFreeEnergy d q t n = -(fc_u d q t n / agl_E d n) + Real.log (1 + Real.exp t) := by
-- proof
  apply StatMech.Walls.fc_edgeFE_eq q t n

/--
[fc_u_le_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_core.lean)
-/
@[path]
private lemma fc_u_le_edges_eq
  {d : ℕ}
  {q : ℝ}
  {t : ℝ}
  {n : ℕ}
-- given
  (hq : 1 ≤ q) :
-- imply
  fc_u d q t n ≤ ((boxGraph d n).edgeFinset.card : ℝ) * (-Real.log (1 - fsc_logistic t)) := by
-- proof
  apply StatMech.Walls.fc_u_le_edges q hq t n

/--
[fc_C_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_core.lean)
-/
@[path]
private lemma fc_C_nonneg_eq
  {d : ℕ}
  {q : ℝ}
-- given
  (hq : 1 ≤ q) :
-- imply
  0 ≤ fc_C q := by
-- proof
  apply StatMech.Walls.fc_C_nonneg hq

/--
[fc_edgeFE_le_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_core.lean)
-/
@[path]
private lemma fc_edgeFE_le_const_eq
  {d : ℕ}
  {d n : ℕ}
  {q : ℝ}
  {s : ℝ}
-- given
  (hd : 1 ≤ d)
  (hn : 1 ≤ n)
  (hq : 1 ≤ q)
  (hE : 0 < (boxGraph d n).edgeFinset.card) :
-- imply
  fc_edgeFreeEnergy d q s n ≤ fc_C q + Real.log (1 + Real.exp s) := by
-- proof
  apply StatMech.Walls.fc_edgeFE_le_const d n hd hn hq s hE

/--
[fc_box_neglog_doubling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_core.lean)
-/
@[path]
private lemma fc_box_neglog_doubling_eq
  {d : ℕ}
  {d K : ℕ}
  {q : ℝ}
  {t : ℝ}
-- given
  (hq : 1 ≤ q) :
-- imply
  fc_u d q t (2 * K + 1) ≤ (2 : ℝ) ^ d * fc_u d q t K + ((2 * d * (qp_Jset d K).card + (2 ^ d + 1) * (2 * d * (qp_Jset d K).card) : ℕ) : ℝ) * (-Real.log (1 - fsc_logistic t)) := by
-- proof
  apply StatMech.Walls.fc_box_neglog_doubling d K hq t

/--
[fc_additiveDoublingBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_core.lean)
-/
@[path]
private lemma fc_additiveDoublingBound_eq
  {d : ℕ}
  {d : ℕ}
  {q : ℝ}
  {t : ℝ}
-- given
  (hd : 1 ≤ d)
  (hq : 1 ≤ q) :
-- imply
  fc_AdditiveDoublingBound d q t := by
-- proof
  apply StatMech.Walls.fc_additiveDoublingBound d hd hq t

/--
[fc_box_vanHove_subadd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_core.lean)
-/
@[path]
private lemma fc_box_vanHove_subadd_eq
  {d : ℕ}
  {m n : ℕ}
  {q : ℝ}
  {t : ℝ}
-- given
  (hq : 1 ≤ q) :
-- imply
  fc_u d q t n ≤ ((ecz_T m n) ^ d : ℝ) * fc_u d q t m + (((boxGraph d n).edgeFinset.card : ℝ) - ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ)) * (-Real.log (1 - fsc_logistic t)) := by
-- proof
  apply StatMech.Walls.fc_box_vanHove_subadd m n hq t

/--
[fc_perEdge_vanHove](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_core.lean)
-/
@[path]
private lemma fc_perEdge_vanHove_eq
  {d : ℕ}
  {m n : ℕ}
  {q : ℝ}
  {s : ℝ}
-- given
  (hq : 1 ≤ q)
  (hEn : 0 < (boxGraph d n).edgeFinset.card)
  (hEm : 0 < (boxGraph d m).edgeFinset.card) :
-- imply
  fc_f d q s n ≤ (((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ) / ((boxGraph d n).edgeFinset.card : ℝ)) * fc_f d q s m + (1 - ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ) / ((boxGraph d n).edgeFinset.card : ℝ)) * (-Real.log (1 - fsc_logistic s)) := by
-- proof
  apply StatMech.Walls.fc_perEdge_vanHove m n hq s hEn hEm

/--
[fc_dyadic_f_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_core.lean)
-/
@[path]
private lemma fc_dyadic_f_tendsto_eq
  {d : ℕ}
  {q : ℝ}
  {s : ℝ}
-- given
  (hd : 1 ≤ d)
  (hq : 1 ≤ q)
  (hbox : ∀ j, 0 < (boxGraph d (agl_K j)).edgeFinset.card) :
-- imply
  ∃ L : ℝ, Tendsto (fun j => fc_f d q s (agl_K j)) atTop (𝓝 L) := by
-- proof
  apply StatMech.Walls.fc_dyadic_f_tendsto hd hq s hbox

/--
[fc_f_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_core.lean)
-/
@[path]
private lemma fc_f_lower_eq
  {d : ℕ}
  {q : ℝ}
  {s : ℝ}
  {n : ℕ}
  {L : ℝ}
-- given
  (hd : 1 ≤ d)
  (hq : 1 ≤ q)
  (hn : 1 ≤ n)
  (hbox : ∀ k, 1 ≤ k → 0 < (boxGraph d k).edgeFinset.card)
  (hL : Tendsto (fun j => fc_f d q s (agl_K j)) atTop (𝓝 L)) :
-- imply
  ((2 * (n : ℝ) + 1) / (2 * n)) * L - (-Real.log (1 - fsc_logistic s)) / (2 * n) ≤ fc_f d q s n := by
-- proof
  apply StatMech.Walls.fc_f_lower hd hq s n hn hbox L hL

/--
[fc_g_dyadic_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_core.lean)
-/
@[path]
private lemma fc_g_dyadic_tendsto_eq
  {d : ℕ}
  {q : ℝ}
  {s : ℝ}
  {L : ℝ}
-- given
  (hL : Tendsto (fun j => fc_f d q s (agl_K j)) atTop (𝓝 L)) :
-- imply
  Tendsto (fun j => fc_g d q s (agl_K j)) atTop (𝓝 L) := by
-- proof
  apply StatMech.Walls.fc_g_dyadic_tendsto s L hL

/--
[fc_upperSeq_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_core.lean)
-/
@[path]
private lemma fc_upperSeq_tendsto_eq
  {d : ℕ}
  {q : ℝ}
  {s : ℝ}
  {m : ℕ}
-- given
  (hd : 1 ≤ d)
  (hm : 1 ≤ m) :
-- imply
  Tendsto (fun n => (((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ) / ((boxGraph d n).edgeFinset.card : ℝ)) * fc_f d q s m + (1 - ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ) / ((boxGraph d n).edgeFinset.card : ℝ)) * (-Real.log (1 - fsc_logistic s))) atTop (𝓝 (fc_g d q s m)) := by
-- proof
  apply StatMech.Walls.fc_upperSeq_tendsto hd s m hm

/--
[fc_perEdgeDensityConverges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_core.lean)
-/
@[path]
private lemma fc_perEdgeDensityConverges_eq
  {d : ℕ}
  {q : ℝ}
  {s : ℝ}
-- given
  (hd : 1 ≤ d)
  (hq : 1 ≤ q)
  (hbox : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card) :
-- imply
  ∃ ρ : ℝ, Tendsto (fun n => fc_u d q s n / ((boxGraph d n).edgeFinset.card : ℝ)) atTop (𝓝 ρ) := by
-- proof
  apply StatMech.Walls.fc_perEdgeDensityConverges hd hq s hbox

/--
[fc_perEdgeDensityConverges_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_core.lean)
-/
@[path]
private lemma fc_perEdgeDensityConverges_unconditional_eq
  {d : ℕ}
  {q : ℝ}
  {s : ℝ}
-- given
  (hd : 1 ≤ d)
  (hq : 1 ≤ q) :
-- imply
  fc_PerEdgeDensityConverges d q s := by
-- proof
  apply StatMech.Walls.fc_perEdgeDensityConverges_unconditional hd hq s

/--
[fc_perEdgeDensityConverges_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_core.lean)
-/
@[path]
private lemma fc_perEdgeDensityConverges_two_eq
  {d : ℕ}
  {s : ℝ} :
-- imply
  fc_PerEdgeDensityConverges d 2 s ↔ ecz_PerEdgeDensityConverges d s := by
-- proof
  apply StatMech.Walls.fc_perEdgeDensityConverges_two s

/--
[fc_core_report](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_core.lean)
-/
@[path]
private lemma fc_core_report_eq
  {d : ℕ} :
-- imply
  True := by
-- proof
  apply StatMech.Walls.fc_core_report


-- created on 2026-10-23
