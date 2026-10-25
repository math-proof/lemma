import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Percolation.CylinderDerivative
open MeasureTheory ProbabilityTheory Function Filter StatMech StatMech.Percolation


/--
[measureProb_eq_measure_real](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CylinderDerivative.lean)
-/
@[path]
private lemma measureProb_eq_measure_real_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  measureProb A (p : ℝ) = (bernoulliProductMeasure (E := E) p hp).real A := by
-- proof
  apply StatMech.Percolation.measureProb_eq_measure_real A p hp

/--
[measureProb_eq_prob](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CylinderDerivative.lean)
-/
@[path]
private lemma measureProb_eq_prob_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {p : ℝ}
-- given
  (h0 : 0 ≤ p)
  (h1 : p ≤ 1) :
-- imply
  measureProb A p = prob p A := by
-- proof
  apply StatMech.Percolation.measureProb_eq_prob A h0 h1

/--
[measureProb_eventuallyEq_prob](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CylinderDerivative.lean)
-/
@[path]
private lemma measureProb_eventuallyEq_prob_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {p : ℝ}
-- given
  (h0 : 0 < p)
  (h1 : p < 1) :
-- imply
  (fun q => measureProb A q) =ᶠ[nhds p] (fun q => prob q A) := by
-- proof
  apply StatMech.Percolation.measureProb_eventuallyEq_prob A h0 h1

/--
[russo_derivative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CylinderDerivative.lean)
-/
@[path]
private lemma russo_derivative_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {p : ℝ}
-- given
  (hA : IsIncreasing A)
  (h0 : 0 < p)
  (h1 : p < 1) :
-- imply
  HasDerivAt (fun p => measureProb A p) (∑ e, pivotalProb p A e) p := by
-- proof
  apply StatMech.Percolation.russo_derivative A hA h0 h1

/--
[russo_formula](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CylinderDerivative.lean)
-/
@[path]
private lemma russo_formula_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {p : ℝ}
-- given
  (hA : IsIncreasing A)
  (h0 : 0 < p)
  (h1 : p < 1) :
-- imply
  deriv (fun p => measureProb A p) p = ∑ e, pivotalProb p A e := by
-- proof
  apply StatMech.Percolation.russo_formula A hA h0 h1

/--
[russo_derivative_measure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CylinderDerivative.lean)
-/
@[path]
private lemma russo_derivative_measure_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
-- given
  (hA : IsIncreasing A)
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (h0 : 0 < (p : ℝ))
  (h1 : (p : ℝ) < 1) :
-- imply
  HasDerivAt (fun q => measureProb A q) (∑ e, pivotalProb (p : ℝ) A e) (p : ℝ) ∧ measureProb A (p : ℝ) = (bernoulliProductMeasure (E := E) p hp).real A := by
-- proof
  apply StatMech.Percolation.russo_derivative_measure A hA p hp h0 h1


-- created on 2026-10-23
