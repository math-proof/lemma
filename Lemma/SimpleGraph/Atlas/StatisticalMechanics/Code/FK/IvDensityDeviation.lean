import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.IvDensityDeviation.Part3
open MeasureTheory Filter Topology SimpleGraph Set StatMech StatMech.FK


/--
[ivd_innerEdgeLE_refl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IvDensityDeviation.lean)
-/
@[path]
private lemma ivd_innerEdgeLE_refl_eq
  {d : ℕ}
  {n : ℕ}
  {eb : Sym2 (boxVerts d n)} :
-- imply
  innerEdgeLE d (le_refl n) eb = eb := by
-- proof
  apply StatMech.FK.ivd_innerEdgeLE_refl n eb

/--
[ivd_freeMeanOpenCount_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IvDensityDeviation.lean)
-/
@[path]
private lemma ivd_freeMeanOpenCount_le_eq
  {d : ℕ}
  {n : ℕ}
  {p a : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hhom : ∀ e ∈ (boxGraph d n).edgeFinset, freeEdgeDensity d 2 (edgeIncl d n e) p = a) :
-- imply
  fkMeanOpenCount (boxGraph d n) p 2 ≤ a * ((boxGraph d n).edgeFinset.card : ℝ) := by
-- proof
  apply StatMech.FK.ivd_freeMeanOpenCount_le n hp hp1 hhom

/--
[ivd_wiredMeanOpenCount_eq_sum_marginals](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IvDensityDeviation.lean)
-/
@[path]
private lemma ivd_wiredMeanOpenCount_eq_sum_marginals_eq
  {d : ℕ}
  {n : ℕ}
  {p : ℝ} :
-- imply
  (∑ ω : ConfigSpace (Sym2 (boxVerts d n)), (chOpenCount (boxGraph d n) ω : ℝ) * wiredFkProb (boxGraph d n) (boxBoundary d n) p 2 ω) = ∑ e ∈ (boxGraph d n).edgeFinset, edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) p 2) e := by
-- proof
  apply StatMech.FK.ivd_wiredMeanOpenCount_eq_sum_marginals n p

/--
[ivd_wiredMeanOpenCount_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IvDensityDeviation.lean)
-/
@[path]
private lemma ivd_wiredMeanOpenCount_ge_eq
  {d : ℕ}
  {n : ℕ}
  {p b : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hhom : ∀ e ∈ (boxGraph d n).edgeFinset, wiredEdgeDensity d 2 (edgeIncl d n e) p = b) :
-- imply
  b * ((boxGraph d n).edgeFinset.card : ℝ) ≤ ∑ ω : ConfigSpace (Sym2 (boxVerts d n)), (chOpenCount (boxGraph d n) ω : ℝ) * wiredFkProb (boxGraph d n) (boxBoundary d n) p 2 ω := by
-- proof
  apply StatMech.FK.ivd_wiredMeanOpenCount_ge n hp hp1 hhom

/--
[den_openCount_upper_deviation_iv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IvDensityDeviation.lean)
-/
@[path]
private lemma den_openCount_upper_deviation_iv_eq
  {d : ℕ}
  {n : ℕ}
  {p a : ℝ}
  {ε : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (ha0 : 0 ≤ a)
  (hhom : ∀ e ∈ (boxGraph d n).edgeFinset, freeEdgeDensity d 2 (edgeIncl d n e) p = a)
  (hε : 0 < ε)
  (hεa : ε ≤ 1 - a)
  (hEpos : 0 < ((boxGraph d n).edgeFinset.card : ℝ)) :
-- imply
  ε ≤ fkOpenCountLeProb (boxGraph d n) p 2 ((a + ε) * ((boxGraph d n).edgeFinset.card : ℝ)) := by
-- proof
  apply StatMech.FK.den_openCount_upper_deviation_iv n hp hp1 ha0 hhom hε hεa hEpos

/--
[den_openCount_lower_deviation_iv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IvDensityDeviation.lean)
-/
@[path]
private lemma den_openCount_lower_deviation_iv_eq
  {d : ℕ}
  {n : ℕ}
  {p b : ℝ}
  {ε : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hb1 : b ≤ 1)
  (hhom : ∀ e ∈ (boxGraph d n).edgeFinset, wiredEdgeDensity d 2 (edgeIncl d n e) p = b)
  (hε : 0 < ε)
  (hεb : ε ≤ b)
  (hEpos : 0 < ((boxGraph d n).edgeFinset.card : ℝ)) :
-- imply
  ε ≤ ivd_wiredOpenCountGeProb d n p ((b - ε) * ((boxGraph d n).edgeFinset.card : ℝ)) := by
-- proof
  apply StatMech.FK.den_openCount_lower_deviation_iv n hp hp1 hb1 hhom hε hεb hEpos

/--
[ivd_freeEdgeDensity_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IvDensityDeviation.lean)
-/
@[path]
private lemma ivd_freeEdgeDensity_nonneg_eq
  {d : ℕ}
  {n : ℕ}
  {e : Sym2 (boxVerts d n)}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  0 ≤ freeEdgeDensity d 2 (edgeIncl d n e) p := by
-- proof
  apply StatMech.FK.ivd_freeEdgeDensity_nonneg n e hp hp1

/--
[ivd_freeEdgeDensity_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IvDensityDeviation.lean)
-/
@[path]
private lemma ivd_freeEdgeDensity_le_one_eq
  {d : ℕ}
  {n : ℕ}
  {e : Sym2 (boxVerts d n)}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  freeEdgeDensity d 2 (edgeIncl d n e) p ≤ 1 := by
-- proof
  apply StatMech.FK.ivd_freeEdgeDensity_le_one n e hp hp1

/--
[ivd_wiredEdgeDensity_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IvDensityDeviation.lean)
-/
@[path]
private lemma ivd_wiredEdgeDensity_le_one_eq
  {d : ℕ}
  {n : ℕ}
  {e : Sym2 (boxVerts d n)}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  wiredEdgeDensity d 2 (edgeIncl d n e) p ≤ 1 := by
-- proof
  apply StatMech.FK.ivd_wiredEdgeDensity_le_one n e hp hp1

/--
[ivd_freeAvgDensity_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IvDensityDeviation.lean)
-/
@[path]
private lemma ivd_freeAvgDensity_nonneg_eq
  {d : ℕ}
  {n : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  0 ≤ ivd_freeAvgDensity d n p := by
-- proof
  apply StatMech.FK.ivd_freeAvgDensity_nonneg n hp hp1

/--
[ivd_freeAvgDensity_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IvDensityDeviation.lean)
-/
@[path]
private lemma ivd_freeAvgDensity_le_one_eq
  {d : ℕ}
  {n : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hEpos : 0 < ((boxGraph d n).edgeFinset.card : ℝ)) :
-- imply
  ivd_freeAvgDensity d n p ≤ 1 := by
-- proof
  apply StatMech.FK.ivd_freeAvgDensity_le_one n hp hp1 hEpos

/--
[ivd_wiredAvgDensity_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IvDensityDeviation.lean)
-/
@[path]
private lemma ivd_wiredAvgDensity_le_one_eq
  {d : ℕ}
  {n : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hEpos : 0 < ((boxGraph d n).edgeFinset.card : ℝ)) :
-- imply
  ivd_wiredAvgDensity d n p ≤ 1 := by
-- proof
  apply StatMech.FK.ivd_wiredAvgDensity_le_one n hp hp1 hEpos

/--
[ivd_freeMeanOpenCount_le_avg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IvDensityDeviation.lean)
-/
@[path]
private lemma ivd_freeMeanOpenCount_le_avg_eq
  {d : ℕ}
  {n : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hEpos : 0 < ((boxGraph d n).edgeFinset.card : ℝ)) :
-- imply
  fkMeanOpenCount (boxGraph d n) p 2 ≤ ivd_freeAvgDensity d n p * ((boxGraph d n).edgeFinset.card : ℝ) := by
-- proof
  apply StatMech.FK.ivd_freeMeanOpenCount_le_avg n hp hp1 hEpos

/--
[ivd_wiredMeanOpenCount_ge_avg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IvDensityDeviation.lean)
-/
@[path]
private lemma ivd_wiredMeanOpenCount_ge_avg_eq
  {d : ℕ}
  {n : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hEpos : 0 < ((boxGraph d n).edgeFinset.card : ℝ)) :
-- imply
  ivd_wiredAvgDensity d n p * ((boxGraph d n).edgeFinset.card : ℝ) ≤ ∑ ω : ConfigSpace (Sym2 (boxVerts d n)), (chOpenCount (boxGraph d n) ω : ℝ) * wiredFkProb (boxGraph d n) (boxBoundary d n) p 2 ω := by
-- proof
  apply StatMech.FK.ivd_wiredMeanOpenCount_ge_avg n hp hp1 hEpos

/--
[den_openCount_upper_deviation_iv_avg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IvDensityDeviation.lean)
-/
@[path]
private lemma den_openCount_upper_deviation_iv_avg_eq
  {d : ℕ}
  {n : ℕ}
  {p : ℝ}
  {ε : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hε : 0 < ε)
  (hεa : ε ≤ 1 - ivd_freeAvgDensity d n p)
  (hEpos : 0 < ((boxGraph d n).edgeFinset.card : ℝ)) :
-- imply
  ε ≤ fkOpenCountLeProb (boxGraph d n) p 2 ((ivd_freeAvgDensity d n p + ε) * ((boxGraph d n).edgeFinset.card : ℝ)) := by
-- proof
  apply StatMech.FK.den_openCount_upper_deviation_iv_avg n hp hp1 hε hεa hEpos

/--
[den_openCount_lower_deviation_iv_avg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IvDensityDeviation.lean)
-/
@[path]
private lemma den_openCount_lower_deviation_iv_avg_eq
  {d : ℕ}
  {n : ℕ}
  {p : ℝ}
  {ε : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hε : 0 < ε)
  (hεb : ε ≤ ivd_wiredAvgDensity d n p)
  (hEpos : 0 < ((boxGraph d n).edgeFinset.card : ℝ)) :
-- imply
  ε ≤ ivd_wiredOpenCountGeProb d n p ((ivd_wiredAvgDensity d n p - ε) * ((boxGraph d n).edgeFinset.card : ℝ)) := by
-- proof
  apply StatMech.FK.den_openCount_lower_deviation_iv_avg n hp hp1 hε hεb hEpos


-- created on 2026-10-23
