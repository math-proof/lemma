import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierB.PlusParityPatternMixing
open MeasureTheory Set StatMech StatMech.FrontierB


/--
[currentEvenConfig_eq_not_currentLocalParity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusParityPatternMixing.lean)
-/
@[path]
private lemma currentEvenConfig_eq_not_currentLocalParity_eq
  {m : InfiniteCurrentConfig E}
  {e : E} :
-- imply
  currentEvenConfig m e = !(currentLocalParity m e) := by
-- proof
  apply StatMech.FrontierB.currentEvenConfig_eq_not_currentLocalParity m e

/--
[currentEvenConfig_trace_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusParityPatternMixing.lean)
-/
@[path]
private lemma currentEvenConfig_trace_iff_eq
  [DecidableEq E]
  {m : InfiniteCurrentConfig E}
  {S : Finset E}
-- given
  (odd : ↑S -> Bool) :
-- imply
  (∀ e ∈ S, currentEvenConfig m e = currentParityTraceTarget S odd e) ↔ currentLocalParity (restrictCurrent S m) = odd := by
-- proof
  apply StatMech.FrontierB.currentEvenConfig_trace_iff m S odd

/--
[currentEvenConfig_multiOpen_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusParityPatternMixing.lean)
-/
@[path]
private lemma currentEvenConfig_multiOpen_iff_eq
  {m : InfiniteCurrentConfig E}
  {T : Finset E} :
-- imply
  currentEvenConfig m ∈ fmu_multiOpen T ↔ m ∈ currentParityAvoidCylinder T := by
-- proof
  apply StatMech.FrontierB.currentEvenConfig_multiOpen_iff m T

/--
[currentParityPattern_indicator_eq_avoid_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusParityPatternMixing.lean)
-/
@[path]
private lemma currentParityPattern_indicator_eq_avoid_sum_eq
  [DecidableEq E]
  {S : Finset E}
  {m : InfiniteCurrentConfig E}
-- given
  (odd : ↑S -> Bool) :
-- imply
  (currentParityPatternCylinder S odd).indicator (fun _ => (1 : Real)) m = ∑ T ∈ S.powerset, currentParityTraceCoeff S odd T * (currentParityAvoidCylinder T).indicator (fun _ => (1 : Real)) m := by
-- proof
  apply StatMech.FrontierB.currentParityPattern_indicator_eq_avoid_sum S odd m

/--
[currentParityPattern_real_eq_avoid_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusParityPatternMixing.lean)
-/
@[path]
private lemma currentParityPattern_real_eq_avoid_sum_eq
  [Countable E]
  [DecidableEq E]
  {mu : Measure (InfiniteCurrentConfig E)}
  [IsProbabilityMeasure mu]
  {S : Finset E}
-- given
  (odd : ↑S -> Bool) :
-- imply
  mu.real (currentParityPatternCylinder S odd) = ∑ T ∈ S.powerset, currentParityTraceCoeff S odd T * mu.real (currentParityAvoidCylinder T) := by
-- proof
  apply StatMech.FrontierB.currentParityPattern_real_eq_avoid_sum mu S odd

/--
[infinitePlusCurrentMeasure_parityPattern_real_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusParityPatternMixing.lean)
-/
@[path]
private lemma infinitePlusCurrentMeasure_parityPattern_real_eq_eq
  {d : Nat}
  {beta : Real}
  {S : Finset (Sym2 (Site d))}
-- given
  (hbeta : 0 < beta)
  (odd : ↑S -> Bool)
  (hS : (↑S : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet) :
-- imply
  (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real (currentParityPatternCylinder S odd) = ∑ T ∈ S.powerset, currentParityTraceCoeff S odd T * ((∫ omega, Real.exp (-beta * edgeSpinSum T omega) ∂(plusState d beta 0 : Measure (ConfigSpace (Site d)))) * Real.cosh beta ^ T.card) := by
-- proof
  apply StatMech.FrontierB.infinitePlusCurrentMeasure_parityPattern_real_eq hbeta S odd hS

/--
[plusParityPatternSpinPolynomial_eq_multiOpenExpansion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusParityPatternMixing.lean)
-/
@[path]
private lemma plusParityPatternSpinPolynomial_eq_multiOpenExpansion_eq
  {d : Nat}
  {beta : Real}
  {S : Finset (Sym2 (Site d))}
  {omega : ConfigSpace (Site d)}
-- given
  (odd : ↑S -> Bool)
  (hS : ∀ e ∈ S, ¬ e.IsDiag) :
-- imply
  plusParityPatternSpinPolynomial beta S odd omega = ∑ i ∈ plusParityExpansionIndices S, plusParityExpansionCoeff beta S odd i * fmu_moInd (plusParityExpansionSupport i) omega := by
-- proof
  apply StatMech.FrontierB.plusParityPatternSpinPolynomial_eq_multiOpenExpansion beta S odd hS omega

/--
[integral_plusParityPatternSpinPolynomial_eq_multiOpenExpansion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusParityPatternMixing.lean)
-/
@[path]
private lemma integral_plusParityPatternSpinPolynomial_eq_multiOpenExpansion_eq
  {d : Nat}
  {mu : Measure (ConfigSpace (Site d))}
  [IsProbabilityMeasure mu]
  {beta : Real}
  {S : Finset (Sym2 (Site d))}
-- given
  (odd : ↑S -> Bool)
  (hS : ∀ e ∈ S, ¬ e.IsDiag) :
-- imply
  (∫ omega, plusParityPatternSpinPolynomial beta S odd omega ∂mu) = ∑ i ∈ plusParityExpansionIndices S, plusParityExpansionCoeff beta S odd i * mu.real (fmu_multiOpen (plusParityExpansionSupport i)) := by
-- proof
  apply StatMech.FrontierB.integral_plusParityPatternSpinPolynomial_eq_multiOpenExpansion mu beta S odd hS

/--
[infinitePlusCurrentMeasure_parityPattern_real_eq_integral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusParityPatternMixing.lean)
-/
@[path]
private lemma infinitePlusCurrentMeasure_parityPattern_real_eq_integral_eq
  {d : Nat}
  {beta : Real}
  {S : Finset (Sym2 (Site d))}
-- given
  (hbeta : 0 < beta)
  (odd : ↑S -> Bool)
  (hS : (↑S : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet) :
-- imply
  (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real (currentParityPatternCylinder S odd) = ∫ omega, plusParityPatternSpinPolynomial beta S odd omega ∂(plusState d beta 0 : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.FrontierB.infinitePlusCurrentMeasure_parityPattern_real_eq_integral hbeta S odd hS

/--
[currentParityPattern_inter_shift_real_eq_avoid_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusParityPatternMixing.lean)
-/
@[path]
private lemma currentParityPattern_inter_shift_real_eq_avoid_sum_eq
  [Countable E]
  [DecidableEq E]
  [Group H]
  [MulAction H E]
  {mu : Measure (InfiniteCurrentConfig E)}
  [IsProbabilityMeasure mu]
  {g : H}
  {S S' : Finset E}
-- given
  (odd : ↑S -> Bool)
  (odd' : ↑S' -> Bool) :
-- imply
  mu.real (currentParityPatternCylinder S odd ∩ (currentShift g) ⁻¹' currentParityPatternCylinder S' odd') = ∑ T ∈ S.powerset, ∑ U ∈ S'.powerset, currentParityTraceCoeff S odd T * currentParityTraceCoeff S' odd' U * mu.real (currentParityAvoidCylinder T ∩ (currentShift g) ⁻¹' currentParityAvoidCylinder U) := by
-- proof
  apply StatMech.FrontierB.currentParityPattern_inter_shift_real_eq_avoid_sum mu g S S' odd odd'

/--
[integrable_exp_neg_edgeSpinSum_mul_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusParityPatternMixing.lean)
-/
@[path]
private lemma integrable_exp_neg_edgeSpinSum_mul_shift_eq
  {d : Nat}
  {mu : Measure (ConfigSpace (Site d))}
  [IsProbabilityMeasure mu]
  {beta : Real}
  {g : Multiplicative (Site d)}
  {F F' : Finset (Sym2 (Site d))}
-- given
  (hF : ∀ e ∈ F, ¬ e.IsDiag)
  (hF' : ∀ e ∈ F', ¬ e.IsDiag) :
-- imply
  Integrable (fun omega => Real.exp (-beta * edgeSpinSum F omega) * Real.exp (-beta * edgeSpinSum F' (shift g omega))) mu := by
-- proof
  apply StatMech.FrontierB.integrable_exp_neg_edgeSpinSum_mul_shift mu beta g F F' hF hF'

/--
[infinitePlusCurrentMeasure_parityPattern_inter_shift_real_eq_integral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusParityPatternMixing.lean)
-/
@[path]
private lemma infinitePlusCurrentMeasure_parityPattern_inter_shift_real_eq_integral_eq
  {d : Nat}
  {beta : Real}
  {g : Multiplicative (Site d)}
  {S S' : Finset (Sym2 (Site d))}
-- given
  (hbeta : 0 < beta)
  (odd : ↑S -> Bool)
  (odd' : ↑S' -> Bool)
  (hS : (↑S : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet)
  (hS' : (↑S' : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet)
  (hdisj : Disjoint S (currentShiftFinset g S')) :
-- imply
  (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real (currentParityPatternCylinder S odd ∩ (currentShift g) ⁻¹' currentParityPatternCylinder S' odd') = ∫ omega, plusParityPatternSpinPolynomial beta S odd omega * plusParityPatternSpinPolynomial beta S' odd' (shift g omega) ∂(plusState d beta 0 : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.FrontierB.infinitePlusCurrentMeasure_parityPattern_inter_shift_real_eq_integral hbeta g S S' odd odd' hS hS' hdisj

/--
[infinitePlusCurrentMeasure_parityPattern_pairMixing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusParityPatternMixing.lean)
-/
@[path]
private lemma infinitePlusCurrentMeasure_parityPattern_pairMixing_eq
  {d : Nat}
  {beta : Real}
  {S S' : Finset (Sym2 (Site d))}
  {epsilon : Real}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta)
  (odd : ↑S -> Bool)
  (odd' : ↑S' -> Bool)
  (hS : (↑S : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet)
  (hS' : (↑S' : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ g : Multiplicative (Site d), Disjoint S (currentShiftFinset g S') ∧ abs ((infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real (currentParityPatternCylinder S odd ∩ (currentShift g) ⁻¹' currentParityPatternCylinder S' odd') - (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real (currentParityPatternCylinder S odd) * (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real (currentParityPatternCylinder S' odd')) < epsilon := by
-- proof
  apply StatMech.FrontierB.infinitePlusCurrentMeasure_parityPattern_pairMixing hd hbeta S S' odd odd' hS hS' epsilon hepsilon

/--
[currentMarginalPMF_eq_parity_bind_of_pattern_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusParityPatternMixing.lean)
-/
@[path]
private lemma currentMarginalPMF_eq_parity_bind_of_pattern_factor_eq
  [Countable E]
  [DecidableEq E]
  {mu : ProbabilityMeasure (InfiniteCurrentConfig E)}
  {S : Finset E}
  {beta : Real}
-- given
  (hbeta : 0 < beta)
  (hfactor : ∀ a : ↑S -> Nat, (mu : Measure _).real (currentCylinder S {a}) = (mu : Measure _).real (currentParityPatternCylinder S (currentLocalParity a)) * ENNReal.toReal (finiteParityPMF S beta hbeta (currentLocalParity a) a)) :
-- imply
  (currentMarginal mu S : Measure (↑S -> Nat)).toPMF = (currentParityMarginalPMF mu S).bind (finiteParityPMF S beta hbeta) := by
-- proof
  apply StatMech.FrontierB.currentMarginalPMF_eq_parity_bind_of_pattern_factor mu S beta hbeta hfactor

/--
[infinitePlusCurrentMarginalPMF_eq_parity_bind](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusParityPatternMixing.lean)
-/
@[path]
private lemma infinitePlusCurrentMarginalPMF_eq_parity_bind_eq
  {d : Nat}
  {beta : Real}
  {S : Finset (Sym2 (Site d))}
-- given
  (hbeta : 0 < beta)
  (hS : (↑S : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet) :
-- imply
  (currentMarginal (infinitePlusCurrentMeasure d beta hbeta.le) S : Measure (↑S -> Nat)).toPMF = (currentParityMarginalPMF (infinitePlusCurrentMeasure d beta hbeta.le) S).bind (finiteParityPMF S beta hbeta) := by
-- proof
  apply StatMech.FrontierB.infinitePlusCurrentMarginalPMF_eq_parity_bind hbeta S hS


-- created on 2026-10-23
