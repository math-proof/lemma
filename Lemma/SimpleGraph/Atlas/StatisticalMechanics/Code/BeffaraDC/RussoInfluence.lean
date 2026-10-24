import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.BeffaraDC.RussoInfluence
open StatMech StatMech.BeffaraDC


/--
[openEdge_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoInfluence.lean)
-/
@[path]
private lemma openEdge_indicator_eq
  [Fintype E]
  [DecidableEq E]
  {e : E}
  {ω : ConfigSpace E} :
-- imply
  (openEdge e).indicator (fun _ => (1 : ℝ)) ω = (if ω e then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.BeffaraDC.openEdge_indicator e ω

/--
[sum_weightOff_true_eta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoInfluence.lean)
-/
@[path]
private lemma sum_weightOff_true_eta_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {e : E} :
-- imply
  ∑ η : {j : E // j ≠ e} → Bool, weightOff p e ((Equiv.funSplitAt e Bool).symm (true, η)) = 1 := by
-- proof
  apply StatMech.BeffaraDC.sum_weightOff_true_eta p e

/--
[sum_filter_true_eq_eta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoInfluence.lean)
-/
@[path]
private lemma sum_filter_true_eq_eta_eq
  [Fintype E]
  [DecidableEq E]
  {e : E}
  {f : ConfigSpace E → ℝ} :
-- imply
  ∑ ω : ConfigSpace E, (if ω e then f ω else 0) = ∑ η : {j : E // j ≠ e} → Bool, f ((Equiv.funSplitAt e Bool).symm (true, η)) := by
-- proof
  apply StatMech.BeffaraDC.sum_filter_true_eq_eta e f

/--
[sum_weightOff_filter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoInfluence.lean)
-/
@[path]
private lemma sum_weightOff_filter_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {e : E} :
-- imply
  ∑ ω : ConfigSpace E, (if ω e then weightOff p e ω else 0) = 1 := by
-- proof
  apply StatMech.BeffaraDC.sum_weightOff_filter p e

/--
[prob_openEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoInfluence.lean)
-/
@[path]
private lemma prob_openEdge_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {e : E} :
-- imply
  prob p (openEdge e) = p := by
-- proof
  apply StatMech.BeffaraDC.prob_openEdge p e

/--
[prob_inter_openEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoInfluence.lean)
-/
@[path]
private lemma prob_inter_openEdge_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {A : Set (ConfigSpace E)}
  {e : E} :
-- imply
  prob p (A ∩ openEdge e) = p * ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * weightOff p e ω * (if ω e then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.BeffaraDC.prob_inter_openEdge p A e

/--
[prob_decompose](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoInfluence.lean)
-/
@[path]
private lemma prob_decompose_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {A : Set (ConfigSpace E)}
  {e : E} :
-- imply
  prob p A = p * (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * weightOff p e ω * (if ω e then (1 : ℝ) else 0)) + (1 - p) * (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * weightOff p e ω * (if ω e then (0 : ℝ) else 1)) := by
-- proof
  apply StatMech.BeffaraDC.prob_decompose p A e

/--
[russo_per_edge_diff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoInfluence.lean)
-/
@[path]
private lemma russo_per_edge_diff_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {A : Set (ConfigSpace E)}
  {e : E}
-- given
  (hA : IsIncreasing A) :
-- imply
  (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * weightOff p e ω * (if ω e then (1 : ℝ) else 0)) - (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * weightOff p e ω * (if ω e then (0 : ℝ) else 1)) = pivotalProb p A e := by
-- proof
  apply StatMech.BeffaraDC.russo_per_edge_diff p A hA e

/--
[cov_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoInfluence.lean)
-/
@[path]
private lemma cov_eq_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {A : Set (ConfigSpace E)}
  {e : E}
-- given
  (hA : IsIncreasing A) :
-- imply
  prob p (A ∩ openEdge e) - prob p (openEdge e) * prob p A = p * (1 - p) * pivotalProb p A e := by
-- proof
  apply StatMech.BeffaraDC.cov_eq p A hA e

/--
[sum_cov_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoInfluence.lean)
-/
@[path]
private lemma sum_cov_eq_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {A : Set (ConfigSpace E)}
-- given
  (hA : IsIncreasing A) :
-- imply
  ∑ e, (prob p (A ∩ openEdge e) - prob p (openEdge e) * prob p A) = p * (1 - p) * ∑ e, pivotalProb p A e := by
-- proof
  apply StatMech.BeffaraDC.sum_cov_eq p A hA

/--
[russoFormula](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoInfluence.lean)
-/
@[path]
private lemma russoFormula_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {A : Set (ConfigSpace E)}
-- given
  (hA : IsIncreasing A)
  (hp0 : p ≠ 0)
  (hp1 : p ≠ 1) :
-- imply
  deriv (fun p => prob p A) p = (1 / (p * (1 - p))) * ∑ e, (prob p (A ∩ openEdge e) - prob p (openEdge e) * prob p A) := by
-- proof
  apply StatMech.BeffaraDC.russoFormula p A hA hp0 hp1

/--
[configWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoInfluence.lean)
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
  apply StatMech.BeffaraDC.configWeight_nonneg hp0 hp1 ω

/--
[pivotalProb_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoInfluence.lean)
-/
@[path]
private lemma pivotalProb_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {A : Set (ConfigSpace E)}
  {e : E}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1) :
-- imply
  0 ≤ pivotalProb p A e := by
-- proof
  apply StatMech.BeffaraDC.pivotalProb_nonneg hp0 hp1 A e

/--
[influence_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoInfluence.lean)
-/
@[path]
private lemma influence_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {A : Set (ConfigSpace E)}
  {e : E}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1) :
-- imply
  0 ≤ influence p A e := by
-- proof
  apply StatMech.BeffaraDC.influence_nonneg hp0 hp1 A e

/--
[cov_ge_influence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoInfluence.lean)
-/
@[path]
private lemma cov_ge_influence_eq
  [Fintype E]
  [DecidableEq E]
  {p ε : ℝ}
  {A : Set (ConfigSpace E)}
  {e : E}
-- given
  (hε0 : 0 < ε)
  (hε1 : ε ≤ 1/2)
  (hpl : ε ≤ p)
  (hpr : p ≤ 1 - ε)
  (hA : IsIncreasing A) :
-- imply
  ε * (1 - ε) * influence p A e ≤ prob p (A ∩ openEdge e) - prob p (openEdge e) * prob p A := by
-- proof
  apply StatMech.BeffaraDC.cov_ge_influence hε0 hε1 hpl hpr A hA e

/--
[deriv_ge_total_influence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoInfluence.lean)
-/
@[path]
private lemma deriv_ge_total_influence_eq
  [Fintype E]
  [DecidableEq E]
  {p ε : ℝ}
  {A : Set (ConfigSpace E)}
-- given
  (hε0 : 0 < ε)
  (hε1 : ε ≤ 1/2)
  (hpl : ε ≤ p)
  (hpr : p ≤ 1 - ε)
  (hA : IsIncreasing A) :
-- imply
  ε * (1 - ε) * ∑ e, influence p A e ≤ deriv (fun p => prob p A) p := by
-- proof
  apply StatMech.BeffaraDC.deriv_ge_total_influence hε0 hε1 hpl hpr A hA

/--
[deriv_eq_total_influence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoInfluence.lean)
-/
@[path]
private lemma deriv_eq_total_influence_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {A : Set (ConfigSpace E)}
-- given
  (hA : IsIncreasing A) :
-- imply
  deriv (fun p => prob p A) p = ∑ e, influence p A e := by
-- proof
  apply StatMech.BeffaraDC.deriv_eq_total_influence p A hA


-- created on 2026-10-23
