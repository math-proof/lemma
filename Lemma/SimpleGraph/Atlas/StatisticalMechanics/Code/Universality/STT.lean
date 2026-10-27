import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.STT.Part4
open MeasureTheory ProbabilityTheory Finset StatMech StatMech.Universality


/--
[isCriticalSquare_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STT.lean)
-/
@[path]
private lemma isCriticalSquare_iff_eq
  {p0 p1 : ℝ} :
-- imply
  IsCriticalSquare p0 p1 ↔ p0 + p1 = 1 := by
-- proof
  apply StatMech.Universality.isCriticalSquare_iff p0 p1

/--
[isCriticalTri_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STT.lean)
-/
@[path]
private lemma isCriticalTri_iff_eq
  {p0 p1 p2 : ℝ} :
-- imply
  IsCriticalTri p0 p1 p2 ↔ p0 + p1 + p2 - p0 * p1 * p2 = 1 := by
-- proof
  apply StatMech.Universality.isCriticalTri_iff p0 p1 p2

/--
[isCriticalTri_iff_isCriticalHex_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STT.lean)
-/
@[path]
private lemma isCriticalTri_iff_isCriticalHex_compl_eq
  {p0 p1 p2 : ℝ} :
-- imply
  IsCriticalTri p0 p1 p2 ↔ IsCriticalHex (1 - p0) (1 - p1) (1 - p2) := by
-- proof
  apply StatMech.Universality.isCriticalTri_iff_isCriticalHex_compl p0 p1 p2

/--
[edgeWeight_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STT.lean)
-/
@[path]
private lemma edgeWeight_true_eq
  {p : ℝ} :
-- imply
  edgeWeight p true = p := by
-- proof
  apply StatMech.Universality.edgeWeight_true p

/--
[edgeWeight_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STT.lean)
-/
@[path]
private lemma edgeWeight_false_eq
  {p : ℝ} :
-- imply
  edgeWeight p false = 1 - p := by
-- proof
  apply StatMech.Universality.edgeWeight_false p

/--
[sum_localWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STT.lean)
-/
@[path]
private lemma sum_localWeight_eq
  {p0 p1 p2 : ℝ} :
-- imply
  ∑ ω : LocalConfig, localWeight p0 p1 p2 ω = 1 := by
-- proof
  apply StatMech.Universality.sum_localWeight p0 p1 p2

/--
[stt_AB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STT.lean)
-/
@[path]
private lemma stt_AB_eq
  {p0 p1 p2 : ℝ} :
-- imply
  triProb p0 p1 p2 triPatAB = starProb (1 - p0) (1 - p1) (1 - p2) starPatAB := by
-- proof
  apply StatMech.Universality.stt_AB p0 p1 p2

/--
[stt_AC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STT.lean)
-/
@[path]
private lemma stt_AC_eq
  {p0 p1 p2 : ℝ} :
-- imply
  triProb p0 p1 p2 triPatAC = starProb (1 - p0) (1 - p1) (1 - p2) starPatAC := by
-- proof
  apply StatMech.Universality.stt_AC p0 p1 p2

/--
[stt_BC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STT.lean)
-/
@[path]
private lemma stt_BC_eq
  {p0 p1 p2 : ℝ} :
-- imply
  triProb p0 p1 p2 triPatBC = starProb (1 - p0) (1 - p1) (1 - p2) starPatBC := by
-- proof
  apply StatMech.Universality.stt_BC p0 p1 p2

/--
[stt_ABC_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STT.lean)
-/
@[path]
private lemma stt_ABC_sub_eq
  {p0 p1 p2 : ℝ} :
-- imply
  triProb p0 p1 p2 triPatABC - starProb (1 - p0) (1 - p1) (1 - p2) starPatABC = kappaTri p0 p1 p2 := by
-- proof
  apply StatMech.Universality.stt_ABC_sub p0 p1 p2

/--
[stt_Sep_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STT.lean)
-/
@[path]
private lemma stt_Sep_sub_eq
  {p0 p1 p2 : ℝ} :
-- imply
  triProb p0 p1 p2 triPatSep - starProb (1 - p0) (1 - p1) (1 - p2) starPatSep = -kappaTri p0 p1 p2 := by
-- proof
  apply StatMech.Universality.stt_Sep_sub p0 p1 p2

/--
[stt_ABC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STT.lean)
-/
@[path]
private lemma stt_ABC_eq
  {p0 p1 p2 : ℝ}
-- given
  (h : IsCriticalTri p0 p1 p2) :
-- imply
  triProb p0 p1 p2 triPatABC = starProb (1 - p0) (1 - p1) (1 - p2) starPatABC := by
-- proof
  apply StatMech.Universality.stt_ABC p0 p1 p2 h

/--
[stt_Sep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STT.lean)
-/
@[path]
private lemma stt_Sep_eq
  {p0 p1 p2 : ℝ}
-- given
  (h : IsCriticalTri p0 p1 p2) :
-- imply
  triProb p0 p1 p2 triPatSep = starProb (1 - p0) (1 - p1) (1 - p2) starPatSep := by
-- proof
  apply StatMech.Universality.stt_Sep p0 p1 p2 h

/--
[starTriangle_connectivity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STT.lean)
-/
@[path]
private lemma starTriangle_connectivity_eq
  {p0 p1 p2 : ℝ}
-- given
  (h : IsCriticalTri p0 p1 p2) :
-- imply
  triProb p0 p1 p2 triPatABC = starProb (1 - p0) (1 - p1) (1 - p2) starPatABC ∧ triProb p0 p1 p2 triPatSep = starProb (1 - p0) (1 - p1) (1 - p2) starPatSep ∧ triProb p0 p1 p2 triPatAB = starProb (1 - p0) (1 - p1) (1 - p2) starPatAB ∧ triProb p0 p1 p2 triPatAC = starProb (1 - p0) (1 - p1) (1 - p2) starPatAC ∧ triProb p0 p1 p2 triPatBC = starProb (1 - p0) (1 - p1) (1 - p2) starPatBC := by
-- proof
  apply StatMech.Universality.starTriangle_connectivity p0 p1 p2 h

/--
[isCriticalTri_of_starTriangle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STT.lean)
-/
@[path]
private lemma isCriticalTri_of_starTriangle_eq
  {p0 p1 p2 : ℝ}
-- given
  (h : triProb p0 p1 p2 triPatABC = starProb (1 - p0) (1 - p1) (1 - p2) starPatABC) :
-- imply
  IsCriticalTri p0 p1 p2 := by
-- proof
  apply StatMech.Universality.isCriticalTri_of_starTriangle p0 p1 p2 h

/--
[starTriangle_iff_isCriticalTri](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STT.lean)
-/
@[path]
private lemma starTriangle_iff_isCriticalTri_eq
  {p0 p1 p2 : ℝ} :
-- imply
  (triProb p0 p1 p2 triPatABC = starProb (1 - p0) (1 - p1) (1 - p2) starPatABC) ↔ IsCriticalTri p0 p1 p2 := by
-- proof
  apply StatMech.Universality.starTriangle_iff_isCriticalTri p0 p1 p2

/--
[bernoulliMeasure_map_not](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STT.lean)
-/
@[path]
private lemma bernoulliMeasure_map_not_eq
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  Measure.map (fun b => !b) (bernoulliMeasure p hp) = bernoulliMeasure (1 - p) tsub_le_self := by
-- proof
  apply StatMech.Universality.bernoulliMeasure_map_not p hp

/--
[one_sub_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STT.lean)
-/
@[path]
private lemma one_sub_half_eq :
-- imply
  (1 : ℝ≥0) - 2⁻¹ = 2⁻¹ := by
-- proof
  apply StatMech.Universality.one_sub_half

/--
[half_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STT.lean)
-/
@[path]
private lemma half_le_one_eq :
-- imply
  (2 : ℝ≥0)⁻¹ ≤ 1 := by
-- proof
  apply StatMech.Universality.half_le_one

/--
[bernoulli_selfDual_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STT.lean)
-/
@[path]
private lemma bernoulli_selfDual_half_eq :
-- imply
  Measure.map (fun b => !b) (bernoulliMeasure 2⁻¹ half_le_one) = bernoulliMeasure 2⁻¹ half_le_one := by
-- proof
  apply StatMech.Universality.bernoulli_selfDual_half

/--
[primal_open_iff_dual_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STT.lean)
-/
@[path]
private lemma primal_open_iff_dual_closed_eq
  {ω : ConfigSpace (Sym2 (Lattice.Site 2))}
  {e : Sym2 (Lattice.Site 2)} :
-- imply
  ω e = true ↔ Lattice.dualConfig ω (Lattice.crossEdge e) = false := by
-- proof
  apply StatMech.Universality.primal_open_iff_dual_closed ω e


-- created on 2026-10-23
