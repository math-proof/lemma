import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.IsingFK.PcUpperAllDimensions
open MeasureTheory Filter Topology Set StatMech StatMech.FK StatMech.IsingFK


/--
[bernoulliReduced_boxBdryConnEvent_le_wiredFinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/PcUpperAllDimensions.lean)
-/
@[path]
private lemma bernoulliReduced_boxBdryConnEvent_le_wiredFinite_eq
  {d : ℕ}
  {p : ℝ}
  {n : ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) ⟨reducedDensity p 2, (reducedDensity_mem_Ioo hp hp1 (by norm_num)).1.le⟩ (reducedDensity_mem_Ioo hp hp1 (by norm_num)).2.le).real (boxBdryConnEvent d n) ≤ (wiredFiniteMeasure d n hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) := by
-- proof
  apply StatMech.FK.bernoulliReduced_boxBdryConnEvent_le_wiredFinite hp hp1 n

/--
[bernoulliTheta_reduced_le_fkTheta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/PcUpperAllDimensions.lean)
-/
@[path]
private lemma bernoulliTheta_reduced_le_fkTheta_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  Percolation.theta d ⟨reducedDensity p 2, (reducedDensity_mem_Ioo hp hp1 (by norm_num)).1.le⟩ (reducedDensity_mem_Ioo hp hp1 (by norm_num)).2.le ≤ fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) := by
-- proof
  apply StatMech.FK.bernoulliTheta_reduced_le_fkTheta hp hp1

/--
[bernoulliReduced_boxBdryConnEvent_le_wiredFinite_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/PcUpperAllDimensions.lean)
-/
@[path]
private lemma bernoulliReduced_boxBdryConnEvent_le_wiredFinite_general_eq
  {d : ℕ}
  {p q : ℝ}
  {n : ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) ⟨reducedDensity p q, (reducedDensity_mem_Ioo hp hp1 hq).1.le⟩ (reducedDensity_mem_Ioo hp hp1 hq).2.le).real (boxBdryConnEvent d n) ≤ (wiredFiniteMeasure d n hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) := by
-- proof
  apply StatMech.FK.bernoulliReduced_boxBdryConnEvent_le_wiredFinite_general hp hp1 hq n

/--
[fkgq_boxBdryConnEvent_diag_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/PcUpperAllDimensions.lean)
-/
@[path]
private lemma fkgq_boxBdryConnEvent_diag_antitone_eq
  {d : ℕ}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  Antitone (fun n => (wiredFiniteMeasure d (n + 1) hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d (n + 1))) := by
-- proof
  apply StatMech.FK.fkgq_boxBdryConnEvent_diag_antitone hp hp1 hq

/--
[fkgq_boxBdryConnEvent_diag_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/PcUpperAllDimensions.lean)
-/
@[path]
private lemma fkgq_boxBdryConnEvent_diag_tendsto_eq
  {d : ℕ}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  Tendsto (fun n => (wiredFiniteMeasure d n hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n)) atTop (nhds (fkTheta d hp hp1 (zero_lt_one.trans_le hq) (q := q))) := by
-- proof
  apply StatMech.FK.fkgq_boxBdryConnEvent_diag_tendsto hp hp1 hq

/--
[bernoulliTheta_reduced_le_fkTheta_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/PcUpperAllDimensions.lean)
-/
@[path]
private lemma bernoulliTheta_reduced_le_fkTheta_general_eq
  {d : ℕ}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  Percolation.theta d ⟨reducedDensity p q, (reducedDensity_mem_Ioo hp hp1 hq).1.le⟩ (reducedDensity_mem_Ioo hp hp1 hq).2.le ≤ fkTheta d hp hp1 (zero_lt_one.trans_le hq) (q := q) := by
-- proof
  apply StatMech.FK.bernoulliTheta_reduced_le_fkTheta_general hp hp1 hq

/--
[fkgq_wiredFiniteMeasure_monotone_in_p](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/PcUpperAllDimensions.lean)
-/
@[path]
private lemma fkgq_wiredFiniteMeasure_monotone_in_p_eq
  {d m : ℕ}
  {p1 p2 q : ℝ}
  {A : Set (ConfigSpace (Sym2 (boxVerts d m)))}
-- given
  (hp1 : 0 < p1)
  (hp1' : p1 < 1)
  (hp2 : 0 < p2)
  (hp2' : p2 < 1)
  (hle : p1 ≤ p2)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (wiredFiniteMeasure d m hp1 hp1' (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d m ⁻¹' A) ≤ (wiredFiniteMeasure d m hp2 hp2' (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d m ⁻¹' A) := by
-- proof
  apply StatMech.FK.fkgq_wiredFiniteMeasure_monotone_in_p hp1 hp1' hp2 hp2' hle hq hA

/--
[fkgq_fkTheta_monotone_in_p](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/PcUpperAllDimensions.lean)
-/
@[path]
private lemma fkgq_fkTheta_monotone_in_p_eq
  {d : ℕ}
  {p1 p2 q : ℝ}
-- given
  (hp1 : 0 < p1)
  (hp1' : p1 < 1)
  (hp2 : 0 < p2)
  (hp2' : p2 < 1)
  (hle : p1 ≤ p2)
  (hq : 1 ≤ q) :
-- imply
  fkTheta d hp1 hp1' (zero_lt_one.trans_le hq) (q := q) ≤ fkTheta d hp2 hp2' (zero_lt_one.trans_le hq) (q := q) := by
-- proof
  apply StatMech.FK.fkgq_fkTheta_monotone_in_p hp1 hp1' hp2 hp2' hle hq

/--
[reducedDensity_inverse_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/PcUpperAllDimensions.lean)
-/
@[path]
private lemma reducedDensity_inverse_general_eq
  {r q : ℝ}
-- given
  (hr0 : 0 < r)
  (hr1 : r < 1)
  (hq0 : 0 < q) :
-- imply
  reducedDensity (q * r / (1 - r + q * r)) q = r := by
-- proof
  apply StatMech.FK.reducedDensity_inverse_general hr0 hr1 hq0

/--
[inverseReducedDensity_general_mem_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/PcUpperAllDimensions.lean)
-/
@[path]
private lemma inverseReducedDensity_general_mem_Ioo_eq
  {r q : ℝ}
-- given
  (hr0 : 0 < r)
  (hr1 : r < 1)
  (hq0 : 0 < q) :
-- imply
  0 < q * r / (1 - r + q * r) ∧ q * r / (1 - r + q * r) < 1 := by
-- proof
  apply StatMech.FK.inverseReducedDensity_general_mem_Ioo hr0 hr1 hq0

/--
[fkTheta_pos_of_bernoulliTheta_pos_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/PcUpperAllDimensions.lean)
-/
@[path]
private lemma fkTheta_pos_of_bernoulliTheta_pos_general_eq
  {d : ℕ}
  {r : NNReal}
  {q : ℝ}
-- given
  (hr0 : 0 < r)
  (hr1 : r < 1)
  (hq : 1 ≤ q)
  (htheta : 0 < Percolation.theta d r hr1.le) :
-- imply
  ∃ p : ℝ, ∃ hp : 0 < p, ∃ hp1 : p < 1, 0 < fkTheta d hp hp1 (zero_lt_one.trans_le hq) (q := q) := by
-- proof
  apply StatMech.FK.fkTheta_pos_of_bernoulliTheta_pos_general hr0 hr1 hq htheta

/--
[fkPc_le_of_fkTheta_pos_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/PcUpperAllDimensions.lean)
-/
@[path]
private lemma fkPc_le_of_fkTheta_pos_general_eq
  {d : ℕ}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (htheta : 0 < fkTheta d hp hp1 (zero_lt_one.trans_le hq) (q := q)) :
-- imply
  fkPc d q ≤ p := by
-- proof
  apply StatMech.FK.fkPc_le_of_fkTheta_pos_general hp hp1 hq htheta

/--
[fkPc_lt_one_of_two_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/PcUpperAllDimensions.lean)
-/
@[path]
private lemma fkPc_lt_one_of_two_le_eq
  {d : ℕ}
  {q : ℝ}
-- given
  (hd : 2 ≤ d)
  (hq : 1 ≤ q) :
-- imply
  fkPc d q < 1 := by
-- proof
  apply StatMech.FK.fkPc_lt_one_of_two_le hd hq

/--
[reducedDensity_two_inverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/PcUpperAllDimensions.lean)
-/
@[path]
private lemma reducedDensity_two_inverse_eq
  {r : ℝ}
-- given
  (hr0 : 0 < r)
  (hr1 : r < 1) :
-- imply
  reducedDensity (2 * r / (1 + r)) 2 = r := by
-- proof
  apply StatMech.FK.reducedDensity_two_inverse hr0 hr1

/--
[inverseReducedDensity_two_mem_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/PcUpperAllDimensions.lean)
-/
@[path]
private lemma inverseReducedDensity_two_mem_Ioo_eq
  {r : ℝ}
-- given
  (hr0 : 0 < r)
  (hr1 : r < 1) :
-- imply
  0 < 2 * r / (1 + r) ∧ 2 * r / (1 + r) < 1 := by
-- proof
  apply StatMech.FK.inverseReducedDensity_two_mem_Ioo hr0 hr1

/--
[fkTheta_two_pos_of_bernoulliTheta_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/PcUpperAllDimensions.lean)
-/
@[path]
private lemma fkTheta_two_pos_of_bernoulliTheta_pos_eq
  {d : ℕ}
  {r : NNReal}
-- given
  (hr0 : 0 < r)
  (hr1 : r < 1)
  (hθ : 0 < Percolation.theta d r hr1.le) :
-- imply
  ∃ p : ℝ, ∃ hp : 0 < p, ∃ hp1 : p < 1, 0 < fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) := by
-- proof
  apply StatMech.FK.fkTheta_two_pos_of_bernoulliTheta_pos hr0 hr1 hθ

/--
[fkPc_le_of_fkTheta_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/PcUpperAllDimensions.lean)
-/
@[path]
private lemma fkPc_le_of_fkTheta_pos_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hθ : 0 < fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2)) :
-- imply
  fkPc d 2 ≤ p := by
-- proof
  apply StatMech.FK.fkPc_le_of_fkTheta_pos hp hp1 hθ

/--
[fkPc_two_lt_one_of_two_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/PcUpperAllDimensions.lean)
-/
@[path]
private lemma fkPc_two_lt_one_of_two_le_eq
  {d : ℕ}
-- given
  (hd : 2 ≤ d) :
-- imply
  fkPc d 2 < 1 := by
-- proof
  apply StatMech.FK.fkPc_two_lt_one_of_two_le hd

/--
[ising_transition_at_fkPc_of_two_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/PcUpperAllDimensions.lean)
-/
@[path]
private lemma ising_transition_at_fkPc_of_two_le_eq
  {d : ℕ}
-- given
  (hd : 2 ≤ d) :
-- imply
  0 < pToBeta 2 (fkPc d 2) ∧ (∀ beta, 0 < beta → beta < pToBeta 2 (fkPc d 2) → magnetization d beta = 0) ∧ (∀ beta, pToBeta 2 (fkPc d 2) < beta → 0 < magnetization d beta) := by
-- proof
  apply StatMech.IsingFK.ising_transition_at_fkPc_of_two_le hd

/--
[ising_transition_unconditional_of_two_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/PcUpperAllDimensions.lean)
-/
@[path]
private lemma ising_transition_unconditional_of_two_le_eq
  {d : ℕ}
-- given
  (hd : 2 ≤ d) :
-- imply
  ∃ betaC : ℝ, 0 < betaC ∧ (∀ beta, 0 < beta → beta < betaC → magnetization d beta = 0) ∧ (∀ beta, betaC < beta → 0 < magnetization d beta) := by
-- proof
  apply StatMech.IsingFK.ising_transition_unconditional_of_two_le hd

/--
[isingBetaC_eq_fkPc_of_two_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/PcUpperAllDimensions.lean)
-/
@[path]
private lemma isingBetaC_eq_fkPc_of_two_le_eq
  {d : ℕ}
-- given
  (hd : 2 ≤ d) :
-- imply
  betaC (magnetization d) = -(1 / 2) * Real.log (1 - fkPc d 2) := by
-- proof
  apply StatMech.IsingFK.isingBetaC_eq_fkPc_of_two_le hd


-- created on 2026-10-23
