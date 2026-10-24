import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Sharpness.PivotalFactor
open StatMech StatMech.Sharpness


/--
[sign_eq_pivotalFactor_mul_edgeWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PivotalFactor.lean)
-/
@[path]
private lemma sign_eq_pivotalFactor_mul_edgeWeight_eq
  [Fintype E]
  [DecidableEq E]
  {ω : ConfigSpace E}
  {e : E}
  {p : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  (if ω e then (1 : ℝ) else -1) = ((openInd ω e - p) / (p * (1 - p))) * edgeWeight p ω e := by
-- proof
  apply StatMech.Sharpness.sign_eq_pivotalFactor_mul_edgeWeight ω e hp0 hp1

/--
[weightOff_mul_sign_eq_pivotalFactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PivotalFactor.lean)
-/
@[path]
private lemma weightOff_mul_sign_eq_pivotalFactor_eq
  [Fintype E]
  [DecidableEq E]
  {ω : ConfigSpace E}
  {e : E}
  {p : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  weightOff p e ω * (if ω e then (1 : ℝ) else -1) = ((openInd ω e - p) / (p * (1 - p))) * configWeight p ω := by
-- proof
  apply StatMech.Sharpness.weightOff_mul_sign_eq_pivotalFactor ω e hp0 hp1

/--
[pivotalProb_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PivotalFactor.lean)
-/
@[path]
private lemma pivotalProb_eq_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {e : E}
  {p : ℝ}
-- given
  (hA : IsIncreasing A)
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  pivotalProb p A e = (1 / (p * (1 - p))) * ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * ((openInd ω e - p) * configWeight p ω) := by
-- proof
  apply StatMech.Sharpness.pivotalProb_eq A hA e hp0 hp1

/--
[hasDerivAt_prob_eq_pivotalFactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PivotalFactor.lean)
-/
@[path]
private lemma hasDerivAt_prob_eq_pivotalFactor_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {p : ℝ}
-- given
  (hA : IsIncreasing A)
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  HasDerivAt (fun p => prob p A) ((1 / (p * (1 - p))) * ∑ e, ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * ((openInd ω e - p) * configWeight p ω)) p := by
-- proof
  apply StatMech.Sharpness.hasDerivAt_prob_eq_pivotalFactor A hA hp0 hp1

/--
[deriv_prob_eq_pivotalFactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PivotalFactor.lean)
-/
@[path]
private lemma deriv_prob_eq_pivotalFactor_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {p : ℝ}
-- given
  (hA : IsIncreasing A)
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  deriv (fun p => prob p A) p = (1 / (p * (1 - p))) * ∑ e, ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * ((openInd ω e - p) * configWeight p ω) := by
-- proof
  apply StatMech.Sharpness.deriv_prob_eq_pivotalFactor A hA hp0 hp1

/--
[configWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PivotalFactor.lean)
-/
@[path]
private lemma configWeight_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {ω : ConfigSpace E}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1) :
-- imply
  0 ≤ configWeight p ω := by
-- proof
  apply StatMech.Sharpness.configWeight_nonneg hp0 hp1 ω

/--
[pivotalProb_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PivotalFactor.lean)
-/
@[path]
private lemma pivotalProb_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {p : ℝ}
  {e : E}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1) :
-- imply
  0 ≤ pivotalProb p A e := by
-- proof
  apply StatMech.Sharpness.pivotalProb_nonneg A hp0 hp1 e

/--
[deriv_prob_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PivotalFactor.lean)
-/
@[path]
private lemma deriv_prob_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {p : ℝ}
-- given
  (hA : IsIncreasing A)
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1) :
-- imply
  0 ≤ deriv (fun p => prob p A) p := by
-- proof
  apply StatMech.Sharpness.deriv_prob_nonneg A hA hp0 hp1


-- created on 2026-10-23
