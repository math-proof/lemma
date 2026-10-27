import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Inequalities.Russo
open StatMech


/--
[configWeight_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Russo.lean)
-/
@[path]
private lemma configWeight_eq_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {e : E}
  {ω : ConfigSpace E} :
-- imply
  configWeight p ω = edgeWeight p ω e * weightOff p e ω := by
-- proof
  apply StatMech.configWeight_eq p e ω

/--
[weightOff_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Russo.lean)
-/
@[path]
private lemma weightOff_congr_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {e : E}
  {ω ω' : ConfigSpace E}
-- given
  (h : ∀ e', e' ≠ e → ω e' = ω' e') :
-- imply
  weightOff p e ω = weightOff p e ω' := by
-- proof
  apply StatMech.weightOff_congr p e h

/--
[hasDerivAt_edgeWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Russo.lean)
-/
@[path]
private lemma hasDerivAt_edgeWeight_eq
  [Fintype E]
  [DecidableEq E]
  {ω : ConfigSpace E}
  {e : E}
  {p : ℝ} :
-- imply
  HasDerivAt (fun p => edgeWeight p ω e) (if ω e then 1 else -1) p := by
-- proof
  apply StatMech.hasDerivAt_edgeWeight ω e p

/--
[hasDerivAt_configWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Russo.lean)
-/
@[path]
private lemma hasDerivAt_configWeight_eq
  [Fintype E]
  [DecidableEq E]
  {ω : ConfigSpace E}
  {p : ℝ} :
-- imply
  HasDerivAt (fun p => configWeight p ω) (∑ e, weightOff p e ω * (if ω e then (1 : ℝ) else -1)) p := by
-- proof
  apply StatMech.hasDerivAt_configWeight ω p

/--
[hasDerivAt_prob](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Russo.lean)
-/
@[path]
private lemma hasDerivAt_prob_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {p : ℝ} :
-- imply
  HasDerivAt (fun p => prob p A) (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * ∑ e, weightOff p e ω * (if ω e then (1 : ℝ) else -1)) p := by
-- proof
  apply StatMech.hasDerivAt_prob A p

/--
[setOpen_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Russo.lean)
-/
@[path]
private lemma setOpen_symm_eq
  [Fintype E]
  [DecidableEq E]
  {e : E}
  {b : Bool}
-- given
  (η : {j : E // j ≠ e} → Bool) :
-- imply
  setOpen e ((Equiv.funSplitAt e Bool).symm (b, η)) = (Equiv.funSplitAt e Bool).symm (true, η) := by
-- proof
  apply StatMech.setOpen_symm e b η

/--
[setClosed_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Russo.lean)
-/
@[path]
private lemma setClosed_symm_eq
  [Fintype E]
  [DecidableEq E]
  {e : E}
  {b : Bool}
-- given
  (η : {j : E // j ≠ e} → Bool) :
-- imply
  setClosed e ((Equiv.funSplitAt e Bool).symm (b, η)) = (Equiv.funSplitAt e Bool).symm (false, η) := by
-- proof
  apply StatMech.setClosed_symm e b η

/--
[russo_per_eta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Russo.lean)
-/
@[path]
private lemma russo_per_eta_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {A : Set (ConfigSpace E)}
  {e : E}
  {ωt ωf : ConfigSpace E}
-- given
  (hA : IsIncreasing A)
  (hwo : weightOff p e ωt = weightOff p e ωf)
  (hto : setOpen e ωt = ωt)
  (htc : setClosed e ωt = ωf)
  (ht : ωt e = true)
  (hf : ωf e = false) :
-- imply
  A.indicator (fun _ => (1 : ℝ)) ωt * (weightOff p e ωt * if ωt e then 1 else -1) + A.indicator (fun _ => (1 : ℝ)) ωf * (weightOff p e ωf * if ωf e then 1 else -1) = {ω | IsPivotal e A ω}.indicator (fun _ => (1 : ℝ)) ωt * configWeight p ωt + {ω | IsPivotal e A ω}.indicator (fun _ => (1 : ℝ)) ωf * configWeight p ωf := by
-- proof
  apply StatMech.russo_per_eta p A hA e ωt ωf hwo hto htc ht hf

/--
[russo_per_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Russo.lean)
-/
@[path]
private lemma russo_per_edge_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {A : Set (ConfigSpace E)}
  {e : E}
-- given
  (hA : IsIncreasing A) :
-- imply
  ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * (weightOff p e ω * (if ω e then (1 : ℝ) else -1)) = pivotalProb p A e := by
-- proof
  apply StatMech.russo_per_edge p A hA e

/--
[hasDerivAt_prob_eq_sum_pivotalProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Russo.lean)
-/
@[path]
private lemma hasDerivAt_prob_eq_sum_pivotalProb_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {p : ℝ}
-- given
  (hA : IsIncreasing A) :
-- imply
  HasDerivAt (fun p => prob p A) (∑ e, pivotalProb p A e) p := by
-- proof
  apply StatMech.hasDerivAt_prob_eq_sum_pivotalProb A hA p

/--
[deriv_prob_eq_sum_pivotalProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Russo.lean)
-/
@[path]
private lemma deriv_prob_eq_sum_pivotalProb_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {p : ℝ}
-- given
  (hA : IsIncreasing A) :
-- imply
  deriv (fun p => prob p A) p = ∑ e, pivotalProb p A e := by
-- proof
  apply StatMech.deriv_prob_eq_sum_pivotalProb A hA p


-- created on 2026-10-23
