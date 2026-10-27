import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFiniteRoots.Part2
open StatMech StatMech.FrontierD


/--
[sixVertexHalfFilledBetheRoots_mem_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFiniteRoots.lean)
-/
@[path]
private lemma sixVertexHalfFilledBetheRoots_mem_open_eq
  {c : ℝ}
  {k : ℕ}
-- given
  (hc : 2 < c) :
-- imply
  SixVertexOpenRootSimplex (sixVertexHalfFilledBetheRoots hc k) := by
-- proof
  apply StatMech.FrontierD.sixVertexHalfFilledBetheRoots_mem_open hc k

/--
[sixVertexHalfFilledBetheRoots_is_solution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFiniteRoots.lean)
-/
@[path]
private lemma sixVertexHalfFilledBetheRoots_is_solution_eq
  {c : ℝ}
  {k : ℕ}
-- given
  (hc : 2 < c) :
-- imply
  SixVertexSatisfiesBetheEquations c (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) (sixVertexHalfFilledBetheRoots hc k) := by
-- proof
  apply StatMech.FrontierD.sixVertexHalfFilledBetheRoots_is_solution hc k

/--
[sixVertexHalfFilledBetheRoots_is_multiplicativeSolution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFiniteRoots.lean)
-/
@[path]
private lemma sixVertexHalfFilledBetheRoots_is_multiplicativeSolution_eq
  {c : ℝ}
  {k : ℕ}
-- given
  (hc : 2 < c) :
-- imply
  SixVertexSatisfiesMultiplicativeBetheEquations c (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) (sixVertexHalfFilledBetheRoots hc k) := by
-- proof
  apply StatMech.FrontierD.sixVertexHalfFilledBetheRoots_is_multiplicativeSolution hc k

/--
[sixVertexHalfFilledBetheRoots_phase_ne_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFiniteRoots.lean)
-/
@[path]
private lemma sixVertexHalfFilledBetheRoots_phase_ne_one_eq
  {c : ℝ}
  {k : ℕ}
  {j : Fin ((k + 1) + (k + 1))}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexBethePhase (sixVertexHalfFilledBetheRoots hc k j) ≠ 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexHalfFilledBetheRoots_phase_ne_one hc k j

/--
[sixVertexPositiveHalfBetheRoots_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFiniteRoots.lean)
-/
@[path]
private lemma sixVertexPositiveHalfBetheRoots_pos_eq
  {c : ℝ}
  {k : ℕ}
  {j : Fin (k + 1)}
-- given
  (hc : 2 < c) :
-- imply
  0 < sixVertexPositiveHalfBetheRoots hc k j := by
-- proof
  apply StatMech.FrontierD.sixVertexPositiveHalfBetheRoots_pos hc k j

/--
[sixVertexPositiveHalfBetheRoots_lt_pi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFiniteRoots.lean)
-/
@[path]
private lemma sixVertexPositiveHalfBetheRoots_lt_pi_eq
  {c : ℝ}
  {k : ℕ}
  {j : Fin (k + 1)}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexPositiveHalfBetheRoots hc k j < Real.pi := by
-- proof
  apply StatMech.FrontierD.sixVertexPositiveHalfBetheRoots_lt_pi hc k j

/--
[sixVertexPositiveHalfBetheRoots_strictMono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFiniteRoots.lean)
-/
@[path]
private lemma sixVertexPositiveHalfBetheRoots_strictMono_eq
  {c : ℝ}
  {k : ℕ}
-- given
  (hc : 2 < c) :
-- imply
  StrictMono (sixVertexPositiveHalfBetheRoots hc k) := by
-- proof
  apply StatMech.FrontierD.sixVertexPositiveHalfBetheRoots_strictMono hc k

/--
[prod_sixVertexHalfFilledBetheRoots](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFiniteRoots.lean)
-/
@[path]
private lemma prod_sixVertexHalfFilledBetheRoots_eq
  {c : ℝ}
  {k : ℕ}
  {f : ℝ → ℂ}
-- given
  (hc : 2 < c) :
-- imply
  (∏ i, f (sixVertexHalfFilledBetheRoots hc k i)) = (∏ j, f (sixVertexPositiveHalfBetheRoots hc k j)) * ∏ j, f (-sixVertexPositiveHalfBetheRoots hc k j) := by
-- proof
  apply StatMech.FrontierD.prod_sixVertexHalfFilledBetheRoots hc k f

/--
[sixVertexHalfFilledBetheEigenvalueCandidate_eq_symmetric](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFiniteRoots.lean)
-/
@[path]
private lemma sixVertexHalfFilledBetheEigenvalueCandidate_eq_symmetric_eq
  {c : ℝ}
  {k : ℕ}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexBetheEigenvalueCandidate c (sixVertexHalfFilledBetheRoots hc k) = sixVertexSymmetricBetheEigenvalueCandidate c (sixVertexPositiveHalfBetheRoots hc k) := by
-- proof
  apply StatMech.FrontierD.sixVertexHalfFilledBetheEigenvalueCandidate_eq_symmetric hc k

/--
[sixVertexHalfFilledBetheEigenvalueCandidate_eq_value](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFiniteRoots.lean)
-/
@[path]
private lemma sixVertexHalfFilledBetheEigenvalueCandidate_eq_value_eq
  {c : ℝ}
  {k : ℕ}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexBetheEigenvalueCandidate c (sixVertexHalfFilledBetheRoots hc k) = (sixVertexSymmetricBetheEigenvalueValue c (sixVertexPositiveHalfBetheRoots hc k) : ℂ) := by
-- proof
  apply StatMech.FrontierD.sixVertexHalfFilledBetheEigenvalueCandidate_eq_value hc k

/--
[sixVertexHalfFilledBetheEigenvalueCandidate_isPositiveReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFiniteRoots.lean)
-/
@[path]
private lemma sixVertexHalfFilledBetheEigenvalueCandidate_isPositiveReal_eq
  {c : ℝ}
  {k : ℕ}
-- given
  (hc : 2 < c) :
-- imply
  (sixVertexBetheEigenvalueCandidate c (sixVertexHalfFilledBetheRoots hc k)).im = 0 ∧ 0 < (sixVertexBetheEigenvalueCandidate c (sixVertexHalfFilledBetheRoots hc k)).re := by
-- proof
  apply StatMech.FrontierD.sixVertexHalfFilledBetheEigenvalueCandidate_isPositiveReal hc k

/--
[sixVertexHalfFilledBetheCandidateRate_eq_rootAverage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFiniteRoots.lean)
-/
@[path]
private lemma sixVertexHalfFilledBetheCandidateRate_eq_rootAverage_eq
  {c : ℝ}
  {k : ℕ}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexHalfFilledBetheCandidateRate hc k = Real.log 2 / (sixVertexFourWidth 0 k : ℝ) + sixVertexSymmetricBetheRootAverage c (sixVertexPositiveHalfBetheRootFamily hc) k := by
-- proof
  apply StatMech.FrontierD.sixVertexHalfFilledBetheCandidateRate_eq_rootAverage hc k

/--
[sixVertexSelectedRootAverage_eq_logKernel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFiniteRoots.lean)
-/
@[path]
private lemma sixVertexSelectedRootAverage_eq_logKernel_eq
  {c : ℝ}
  {k : ℕ}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexSymmetricBetheRootAverage c (sixVertexPositiveHalfBetheRootFamily hc) k = (∑ j, Real.log (((c ^ 2 - 1) ^ 2 + 1 + 2 * (c ^ 2 - 1) * Real.cos (sixVertexPositiveHalfBetheRoots hc k j)) / (2 - 2 * Real.cos (sixVertexPositiveHalfBetheRoots hc k j)))) / (sixVertexFourWidth 0 k : ℝ) := by
-- proof
  apply StatMech.FrontierD.sixVertexSelectedRootAverage_eq_logKernel hc k

/--
[sixVertexSelectedLogKernel_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFiniteRoots.lean)
-/
@[path]
private lemma sixVertexSelectedLogKernel_pos_eq
  {c : ℝ}
  {k : ℕ}
  {j : Fin (k + 1)}
-- given
  (hc : 2 < c) :
-- imply
  0 < (((c ^ 2 - 1) ^ 2 + 1 + 2 * (c ^ 2 - 1) * Real.cos (sixVertexPositiveHalfBetheRoots hc k j)) / (2 - 2 * Real.cos (sixVertexPositiveHalfBetheRoots hc k j))) := by
-- proof
  apply StatMech.FrontierD.sixVertexSelectedLogKernel_pos hc k j


-- created on 2026-10-23
