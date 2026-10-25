import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Percolation.RussoFormula
open StatMech StatMech.Percolation


/--
[rus_prod_extract](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/RussoFormula.lean)
-/
@[path]
private lemma rus_prod_extract_eq
  [Fintype E]
  [DecidableEq E]
  {e₀ : E}
  {g : E → Bool → ℝ}
  {ω : ConfigSpace E}
-- given
  (h : Bool → ℝ) :
-- imply
  h (ω e₀) * (∏ e, g e (ω e)) = ∏ e, (if e = e₀ then h (ω e) * g e (ω e) else g e (ω e)) := by
-- proof
  apply StatMech.Percolation.rus_prod_extract e₀ h g ω

/--
[rus_expect_openInd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/RussoFormula.lean)
-/
@[path]
private lemma rus_expect_openInd_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {e₀ : E} :
-- imply
  ∑ ω : ConfigSpace E, openInd ω e₀ * configWeight p ω = p := by
-- proof
  apply StatMech.Percolation.rus_expect_openInd p e₀

/--
[rus_expect_openCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/RussoFormula.lean)
-/
@[path]
private lemma rus_expect_openCount_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ} :
-- imply
  rus_expect p (rus_openCount (E := E)) = (Fintype.card E : ℝ) * p := by
-- proof
  apply StatMech.Percolation.rus_expect_openCount p

/--
[rus_sum_weightOff_sign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/RussoFormula.lean)
-/
@[path]
private lemma rus_sum_weightOff_sign_eq
  [Fintype E]
  [DecidableEq E]
  {ω : ConfigSpace E}
  {p : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  (∑ e, weightOff p e ω * (if ω e then (1 : ℝ) else -1)) = (1 / (p * (1 - p))) * ((rus_openCount ω - (Fintype.card E : ℝ) * p) * configWeight p ω) := by
-- proof
  apply StatMech.Percolation.rus_sum_weightOff_sign ω hp0 hp1

/--
[rus_russo_formula](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/RussoFormula.lean)
-/
@[path]
private lemma rus_russo_formula_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {p : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  HasDerivAt (fun p => prob p A) ((1 / (p * (1 - p))) * (rus_expect p (fun ω => rus_openCount ω * A.indicator (fun _ => (1 : ℝ)) ω) - rus_expect p (rus_openCount (E := E)) * prob p A)) p := by
-- proof
  apply StatMech.Percolation.rus_russo_formula A hp0 hp1

/--
[rus_russo_formula_deriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/RussoFormula.lean)
-/
@[path]
private lemma rus_russo_formula_deriv_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {p : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  deriv (fun p => prob p A) p = (1 / (p * (1 - p))) * (rus_expect p (fun ω => rus_openCount ω * A.indicator (fun _ => (1 : ℝ)) ω) - rus_expect p (rus_openCount (E := E)) * prob p A) := by
-- proof
  apply StatMech.Percolation.rus_russo_formula_deriv A hp0 hp1

/--
[rus_russo_formula_pivotal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/RussoFormula.lean)
-/
@[path]
private lemma rus_russo_formula_pivotal_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {p : ℝ}
-- given
  (hA : IsIncreasing A) :
-- imply
  HasDerivAt (fun p => prob p A) (∑ e, pivotalProb p A e) p := by
-- proof
  apply StatMech.Percolation.rus_russo_formula_pivotal A hA p

/--
[rus_covariance_eq_sum_pivotalProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/RussoFormula.lean)
-/
@[path]
private lemma rus_covariance_eq_sum_pivotalProb_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {p : ℝ}
-- given
  (hA : IsIncreasing A)
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  (1 / (p * (1 - p))) * (rus_expect p (fun ω => rus_openCount ω * A.indicator (fun _ => (1 : ℝ)) ω) - rus_expect p (rus_openCount (E := E)) * prob p A) = ∑ e, pivotalProb p A e := by
-- proof
  apply StatMech.Percolation.rus_covariance_eq_sum_pivotalProb A hA hp0 hp1


-- created on 2026-10-23
