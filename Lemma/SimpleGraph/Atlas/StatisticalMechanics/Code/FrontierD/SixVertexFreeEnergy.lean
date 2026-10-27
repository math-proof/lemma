import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFreeEnergy
open Finset Matrix Filter Topology StatMech StatMech.FrontierD


/--
[sixVertexSector_eigenvalues](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFreeEnergy.lean)
-/
@[path]
private lemma sixVertexSector_eigenvalues_eq
  {N n : ℕ}
  {c : ℝ}
  {i : Fin (Fintype.card (SixVertexSector N n))}
-- given
  (hn : n ≤ N)
  (hc : 0 < c)
  (hi : i ≠ sixVertexSectorTopIndex N n hn) :
-- imply
  (sixVertexSectorTransfer_isHermitian N n c).eigenvalues₀ i ≠ sixVertexSectorTopEigenvalue N n hn c := by
-- proof
  apply StatMech.FrontierD.sixVertexSector_eigenvalues hn hc i hi

/--
[sixVertexSector_trace_div_top_pow_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFreeEnergy.lean)
-/
@[path]
private lemma sixVertexSector_trace_div_top_pow_tendsto_one_eq
  {N n : ℕ}
  {c : ℝ}
-- given
  (hn : n ≤ N)
  (hc : 0 < c) :
-- imply
  Tendsto (fun M : ℕ => Matrix.trace (sixVertexSectorTransfer N n c ^ M) / sixVertexSectorTopEigenvalue N n hn c ^ M) atTop (nhds 1) := by
-- proof
  apply StatMech.FrontierD.sixVertexSector_trace_div_top_pow_tendsto_one hn hc

/--
[sixVertexSector_trace_pow_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFreeEnergy.lean)
-/
@[path]
private lemma sixVertexSector_trace_pow_pos_eq
  {N n : ℕ}
  {c : ℝ}
  {M : ℕ}
-- given
  (hn : n ≤ N)
  (hc : 0 < c) :
-- imply
  0 < Matrix.trace (sixVertexSectorTransfer N n c ^ M) := by
-- proof
  apply StatMech.FrontierD.sixVertexSector_trace_pow_pos hn hc M

/--
[sixVertexSector_log_trace_div_height_tendsto_log_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFreeEnergy.lean)
-/
@[path]
private lemma sixVertexSector_log_trace_div_height_tendsto_log_top_eq
  {N n : ℕ}
  {c : ℝ}
-- given
  (hn : n ≤ N)
  (hc : 0 < c) :
-- imply
  Tendsto (fun M : ℕ => Real.log (Matrix.trace (sixVertexSectorTransfer N n c ^ M)) / (M : ℝ)) atTop (nhds (Real.log (sixVertexSectorTopEigenvalue N n hn c))) := by
-- proof
  apply StatMech.FrontierD.sixVertexSector_log_trace_div_height_tendsto_log_top hn hc

/--
[sixVertexLambda_trace_div_pow_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFreeEnergy.lean)
-/
@[path]
private lemma sixVertexLambda_trace_div_pow_tendsto_one_eq
  {N r : ℕ}
  {c : ℝ}
-- given
  (hN : Even N)
  (hr : r ≤ N / 2)
  (hc : 0 < c) :
-- imply
  Tendsto (fun M : ℕ => Matrix.trace (sixVertexSectorTransfer N (N / 2 - r) c ^ M) / sixVertexLambda N r hN hr c ^ M) atTop (nhds 1) := by
-- proof
  apply StatMech.FrontierD.sixVertexLambda_trace_div_pow_tendsto_one N r hN hr hc

/--
[sixVertexLambda_log_trace_div_height_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFreeEnergy.lean)
-/
@[path]
private lemma sixVertexLambda_log_trace_div_height_tendsto_eq
  {N r : ℕ}
  {c : ℝ}
-- given
  (hN : Even N)
  (hr : r ≤ N / 2)
  (hc : 0 < c) :
-- imply
  Tendsto (fun M : ℕ => Real.log (Matrix.trace (sixVertexSectorTransfer N (N / 2 - r) c ^ M)) / (M : ℝ)) atTop (nhds (Real.log (sixVertexLambda N r hN hr c))) := by
-- proof
  apply StatMech.FrontierD.sixVertexLambda_log_trace_div_height_tendsto N r hN hr hc

/--
[sixVertexLambda_log_trace_ratio_div_height_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFreeEnergy.lean)
-/
@[path]
private lemma sixVertexLambda_log_trace_ratio_div_height_tendsto_eq
  {N r : Nat}
  {c : Real}
-- given
  (hN : Even N)
  (hr : r ≤ N / 2)
  (hc : 0 < c) :
-- imply
  Tendsto (fun M : Nat => Real.log (Matrix.trace (sixVertexSectorTransfer N (N / 2 - r) c ^ M) / Matrix.trace (sixVertexSectorTransfer N (N / 2) c ^ M)) / (M : Real)) atTop (nhds (Real.log (sixVertexLambda N r hN hr c / sixVertexLambda N 0 hN (Nat.zero_le _) c))) := by
-- proof
  apply StatMech.FrontierD.sixVertexLambda_log_trace_ratio_div_height_tendsto N r hN hr hc


-- created on 2026-10-23
