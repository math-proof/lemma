import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricProduct.Part3
open Finset Matrix Filter Topology StatMech StatMech.FrontierD


/--
[sixVertexBethePhase_norm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricProduct.lean)
-/
@[path]
private lemma sixVertexBethePhase_norm_eq
  {p : ℝ} :
-- imply
  ‖sixVertexBethePhase p‖ = 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexBethePhase_norm p

/--
[sixVertexBethePhase_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricProduct.lean)
-/
@[path]
private lemma sixVertexBethePhase_neg_eq
  {p : ℝ} :
-- imply
  sixVertexBethePhase (-p) = star (sixVertexBethePhase p) := by
-- proof
  apply StatMech.FrontierD.sixVertexBethePhase_neg p

/--
[sixVertexBetheM_phase_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricProduct.lean)
-/
@[path]
private lemma sixVertexBetheM_phase_neg_eq
  {c p : ℝ} :
-- imply
  sixVertexBetheM c (sixVertexBethePhase (-p)) = star (sixVertexBetheM c (sixVertexBethePhase p)) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheM_phase_neg c p

/--
[sixVertexBetheL_phase_eq_conj_M](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricProduct.lean)
-/
@[path]
private lemma sixVertexBetheL_phase_eq_conj_M_eq
  {c p : ℝ} :
-- imply
  sixVertexBetheL c (sixVertexBethePhase p) = star (sixVertexBetheM c (sixVertexBethePhase p)) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheL_phase_eq_conj_M c p

/--
[sixVertexBetheM_symmetric_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricProduct.lean)
-/
@[path]
private lemma sixVertexBetheM_symmetric_pair_eq
  {c p : ℝ} :
-- imply
  sixVertexBetheM c (sixVertexBethePhase p) * sixVertexBetheM c (sixVertexBethePhase (-p)) = (Complex.normSq (sixVertexBetheM c (sixVertexBethePhase p)) : ℂ) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheM_symmetric_pair c p

/--
[sixVertexBetheL_symmetric_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricProduct.lean)
-/
@[path]
private lemma sixVertexBetheL_symmetric_pair_eq
  {c p : ℝ} :
-- imply
  sixVertexBetheL c (sixVertexBethePhase p) * sixVertexBetheL c (sixVertexBethePhase (-p)) = (Complex.normSq (sixVertexBetheM c (sixVertexBethePhase p)) : ℂ) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheL_symmetric_pair c p

/--
[sixVertexSymmetricBetheEigenvalueCandidate_eq_value](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricProduct.lean)
-/
@[path]
private lemma sixVertexSymmetricBetheEigenvalueCandidate_eq_value_eq
  {k : ℕ}
  {c : ℝ}
  {p : Fin k → ℝ} :
-- imply
  sixVertexSymmetricBetheEigenvalueCandidate c p = (sixVertexSymmetricBetheEigenvalueValue c p : ℂ) := by
-- proof
  apply StatMech.FrontierD.sixVertexSymmetricBetheEigenvalueCandidate_eq_value c p

/--
[sixVertexSymmetricBetheEigenvalueValue_log](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricProduct.lean)
-/
@[path]
private lemma sixVertexSymmetricBetheEigenvalueValue_log_eq
  {k : ℕ}
  {c : ℝ}
  {p : Fin k → ℝ}
-- given
  (hM : ∀ j, sixVertexBetheM c (sixVertexBethePhase (p j)) ≠ 0) :
-- imply
  Real.log (sixVertexSymmetricBetheEigenvalueValue c p) = Real.log 2 + 2 * ∑ j, Real.log ‖sixVertexBetheM c (sixVertexBethePhase (p j))‖ := by
-- proof
  apply StatMech.FrontierD.sixVertexSymmetricBetheEigenvalueValue_log c p hM

/--
[sixVertexBetheM_phase_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricProduct.lean)
-/
@[path]
private lemma sixVertexBetheM_phase_ne_zero_eq
  {c : ℝ}
  {p : ℝ}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexBetheM c (sixVertexBethePhase p) ≠ 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheM_phase_ne_zero hc p

/--
[sixVertexSymmetricBetheEigenvalueValue_log_of_two_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricProduct.lean)
-/
@[path]
private lemma sixVertexSymmetricBetheEigenvalueValue_log_of_two_lt_eq
  {k : ℕ}
  {c : ℝ}
  {p : Fin k → ℝ}
-- given
  (hc : 2 < c) :
-- imply
  Real.log (sixVertexSymmetricBetheEigenvalueValue c p) = Real.log 2 + 2 * ∑ j, Real.log ‖sixVertexBetheM c (sixVertexBethePhase (p j))‖ := by
-- proof
  apply StatMech.FrontierD.sixVertexSymmetricBetheEigenvalueValue_log_of_two_lt hc p

/--
[sixVertexSymmetricBetheEigenvalueValue_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricProduct.lean)
-/
@[path]
private lemma sixVertexSymmetricBetheEigenvalueValue_pos_eq
  {k : ℕ}
  {c : ℝ}
  {p : Fin k → ℝ}
-- given
  (hc : 2 < c) :
-- imply
  0 < sixVertexSymmetricBetheEigenvalueValue c p := by
-- proof
  apply StatMech.FrontierD.sixVertexSymmetricBetheEigenvalueValue_pos hc p

/--
[sixVertexSymmetricBetheEigenvalueCandidate_isPositiveReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricProduct.lean)
-/
@[path]
private lemma sixVertexSymmetricBetheEigenvalueCandidate_isPositiveReal_eq
  {k : ℕ}
  {c : ℝ}
  {p : Fin k → ℝ}
-- given
  (hc : 2 < c) :
-- imply
  (sixVertexSymmetricBetheEigenvalueCandidate c p).im = 0 ∧ 0 < (sixVertexSymmetricBetheEigenvalueCandidate c p).re := by
-- proof
  apply StatMech.FrontierD.sixVertexSymmetricBetheEigenvalueCandidate_isPositiveReal hc p

/--
[sixVertexBetheM_phase_normSq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricProduct.lean)
-/
@[path]
private lemma sixVertexBetheM_phase_normSq_eq
  {c p : ℝ}
-- given
  (hp : sixVertexBethePhase p ≠ 1) :
-- imply
  Complex.normSq (sixVertexBetheM c (sixVertexBethePhase p)) = ((c ^ 2 - 1) ^ 2 + 1 + 2 * (c ^ 2 - 1) * Real.cos p) / (2 - 2 * Real.cos p) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheM_phase_normSq c p hp

/--
[sixVertexBetheM_phase_log_norm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricProduct.lean)
-/
@[path]
private lemma sixVertexBetheM_phase_log_norm_eq
  {c p : ℝ}
-- given
  (hp : sixVertexBethePhase p ≠ 1) :
-- imply
  Real.log ‖sixVertexBetheM c (sixVertexBethePhase p)‖ = (1 / 2 : ℝ) * Real.log (((c ^ 2 - 1) ^ 2 + 1 + 2 * (c ^ 2 - 1) * Real.cos p) / (2 - 2 * Real.cos p)) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheM_phase_log_norm c p hp

/--
[sixVertexCentralWidthRate_eq_symmetricBetheRootAverage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricProduct.lean)
-/
@[path]
private lemma sixVertexCentralWidthRate_eq_symmetricBetheRootAverage_eq
  {c : ℝ}
  {roots : SixVertexSymmetricHalfFilledRoots}
  {k : ℕ}
-- given
  (hc : 2 < c)
  (hroots : SixVertexHasSymmetricBetheIdentification c roots) :
-- imply
  sixVertexCentralWidthRate c k = Real.log 2 / (sixVertexFourWidth 0 k : ℝ) + sixVertexSymmetricBetheRootAverage c roots k := by
-- proof
  apply StatMech.FrontierD.sixVertexCentralWidthRate_eq_symmetricBetheRootAverage hc roots hroots k

/--
[sixVertexCentralWidthRate_tendsto_iff_symmetricBetheRootAverage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricProduct.lean)
-/
@[path]
private lemma sixVertexCentralWidthRate_tendsto_iff_symmetricBetheRootAverage_eq
  {c a : ℝ}
  {roots : SixVertexSymmetricHalfFilledRoots}
-- given
  (hc : 2 < c)
  (hroots : SixVertexHasSymmetricBetheIdentification c roots) :
-- imply
  Tendsto (sixVertexCentralWidthRate c) atTop (nhds a) ↔ Tendsto (sixVertexSymmetricBetheRootAverage c roots) atTop (nhds a) := by
-- proof
  apply StatMech.FrontierD.sixVertexCentralWidthRate_tendsto_iff_symmetricBetheRootAverage hc roots hroots

/--
[sixVertexSector_eigenvalue_eq_top_of_positive_eigenvector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricProduct.lean)
-/
@[path]
private lemma sixVertexSector_eigenvalue_eq_top_of_positive_eigenvector_eq
  {N n : ℕ}
  {c μ : ℝ}
  {v : SixVertexSector N n → ℝ}
-- given
  (hn : n ≤ N)
  (hc : 0 < c)
  (hv : ∀ i, 0 < v i)
  (heig : sixVertexSectorTransfer N n c *ᵥ v = μ • v) :
-- imply
  μ = sixVertexSectorTopEigenvalue N n hn c := by
-- proof
  apply StatMech.FrontierD.sixVertexSector_eigenvalue_eq_top_of_positive_eigenvector hn hc v hv heig


-- created on 2026-10-23
