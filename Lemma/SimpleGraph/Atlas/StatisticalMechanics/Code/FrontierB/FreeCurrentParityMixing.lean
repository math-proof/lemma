import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.FreeCurrentParityMixing.Part2
open Filter MeasureTheory Set Topology StatMech StatMech.FrontierB


/--
[edgeBoundary_card_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeCurrentParityMixing.lean)
-/
@[path]
private lemma edgeBoundary_card_even_eq
  {d : Nat}
  [DecidableEq V]
  {F : Finset (Sym2 V)}
-- given
  (hF : ∀ e ∈ F, ¬ e.IsDiag) :
-- imply
  Even (edgeBoundary F).card := by
-- proof
  apply StatMech.FrontierB.edgeBoundary_card_even F hF

/--
[infiniteFreeCurrentMeasure_parityAvoid_real_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeCurrentParityMixing.lean)
-/
@[path]
private lemma infiniteFreeCurrentMeasure_parityAvoid_real_eq_eq
  {d : Nat}
  {d : Nat}
  {beta : Real}
  {F : Finset (Sym2 (Site d))}
-- given
  (hbeta : 0 < beta)
  (hF : (↑F : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet) :
-- imply
  (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real (currentParityAvoidCylinder F) = (∫ omega, Real.exp (-beta * edgeSpinSum F omega) ∂(freeState d beta 0 : Measure (ConfigSpace (Site d)))) * Real.cosh beta ^ F.card := by
-- proof
  apply StatMech.FrontierB.infiniteFreeCurrentMeasure_parityAvoid_real_eq hbeta F hF

/--
[infiniteFreeCurrentMeasure_parityAvoid_inter_shift_real_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeCurrentParityMixing.lean)
-/
@[path]
private lemma infiniteFreeCurrentMeasure_parityAvoid_inter_shift_real_eq_eq
  {d : Nat}
  {d : Nat}
  {beta : Real}
  {g : Multiplicative (Site d)}
  {F F' : Finset (Sym2 (Site d))}
-- given
  (hbeta : 0 < beta)
  (hF : (↑F : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet)
  (hF' : (↑F' : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet)
  (hdisj : Disjoint F (currentShiftFinset g F')) :
-- imply
  (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real (currentParityAvoidCylinder F ∩ (currentShift g) ⁻¹' currentParityAvoidCylinder F') = (∫ omega, Real.exp (-beta * edgeSpinSum F omega) * Real.exp (-beta * edgeSpinSum F' (shift g omega)) ∂(freeState d beta 0 : Measure (ConfigSpace (Site d)))) * (Real.cosh beta ^ F.card * Real.cosh beta ^ F'.card) := by
-- proof
  apply StatMech.FrontierB.infiniteFreeCurrentMeasure_parityAvoid_inter_shift_real_eq hbeta g F F' hF hF' hdisj

/--
[infiniteFreeCurrentMeasure_parityPattern_real_eq_integral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeCurrentParityMixing.lean)
-/
@[path]
private lemma infiniteFreeCurrentMeasure_parityPattern_real_eq_integral_eq
  {d : Nat}
  {d : Nat}
  {beta : Real}
  {S : Finset (Sym2 (Site d))}
-- given
  (hbeta : 0 < beta)
  (odd : ↑S -> Bool)
  (hS : (↑S : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet) :
-- imply
  (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real (currentParityPatternCylinder S odd) = ∫ omega, plusParityPatternSpinPolynomial beta S odd omega ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.FrontierB.infiniteFreeCurrentMeasure_parityPattern_real_eq_integral hbeta S odd hS

/--
[infiniteFreeCurrentMeasure_parityPattern_inter_shift_real_eq_integral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeCurrentParityMixing.lean)
-/
@[path]
private lemma infiniteFreeCurrentMeasure_parityPattern_inter_shift_real_eq_integral_eq
  {d : Nat}
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
  (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real (currentParityPatternCylinder S odd ∩ (currentShift g) ⁻¹' currentParityPatternCylinder S' odd') = ∫ omega, plusParityPatternSpinPolynomial beta S odd omega * plusParityPatternSpinPolynomial beta S' odd' (shift g omega) ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.FrontierB.infiniteFreeCurrentMeasure_parityPattern_inter_shift_real_eq_integral hbeta g S S' odd odd' hS hS' hdisj

/--
[plusParityPatternSpinPolynomial_eq_freeEvenExpansion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeCurrentParityMixing.lean)
-/
@[path]
private lemma plusParityPatternSpinPolynomial_eq_freeEvenExpansion_eq
  {d : Nat}
  {d : Nat}
  {beta : Real}
  {S : Finset (Sym2 (Site d))}
  {omega : ConfigSpace (Site d)}
-- given
  (odd : ↑S -> Bool)
  (hS : ∀ e ∈ S, ¬ e.IsDiag) :
-- imply
  plusParityPatternSpinPolynomial beta S odd omega = ∑ i ∈ freeParityExpansionIndices S, freeParityExpansionCoeff beta S odd i * spinProd (freeParityExpansionSupport i) omega := by
-- proof
  apply StatMech.FrontierB.plusParityPatternSpinPolynomial_eq_freeEvenExpansion beta S odd hS omega

/--
[infiniteFreeCurrentMeasure_parityPattern_family_pairMixing_after](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeCurrentParityMixing.lean)
-/
@[path]
private lemma infiniteFreeCurrentMeasure_parityPattern_family_pairMixing_after_eq
  {d : Nat}
  {d : Nat}
  {beta : Real}
  {K : Nat}
  {S : Finset (Sym2 (Site d))}
  {epsilon : Real}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta)
  (hS : (↑S : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet)
  (patterns : Finset (↑S -> Bool))
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ k : Nat, K ≤ k ∧ Disjoint S (currentShiftFinset (FK.freeAxisTranslationPower hd k) S) ∧ ∀ odd ∈ patterns, ∀ odd' ∈ patterns, abs ((infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real (currentParityPatternCylinder S odd ∩ (currentShift (FK.freeAxisTranslationPower hd k)) ⁻¹' currentParityPatternCylinder S odd') - (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real (currentParityPatternCylinder S odd) * (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real (currentParityPatternCylinder S odd')) < epsilon := by
-- proof
  apply StatMech.FrontierB.infiniteFreeCurrentMeasure_parityPattern_family_pairMixing_after hd hbeta K S hS patterns epsilon hepsilon

/--
[infiniteFreeCurrentMeasure_parityPattern_family_pairMixing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeCurrentParityMixing.lean)
-/
@[path]
private lemma infiniteFreeCurrentMeasure_parityPattern_family_pairMixing_eq
  {d : Nat}
  {d : Nat}
  {beta : Real}
  {S : Finset (Sym2 (Site d))}
  {epsilon : Real}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta)
  (hS : (↑S : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet)
  (patterns : Finset (↑S -> Bool))
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ g : Multiplicative (Site d), Disjoint S (currentShiftFinset g S) ∧ ∀ odd ∈ patterns, ∀ odd' ∈ patterns, abs ((infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real (currentParityPatternCylinder S odd ∩ (currentShift g) ⁻¹' currentParityPatternCylinder S odd') - (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real (currentParityPatternCylinder S odd) * (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real (currentParityPatternCylinder S odd')) < epsilon := by
-- proof
  apply StatMech.FrontierB.infiniteFreeCurrentMeasure_parityPattern_family_pairMixing hd hbeta S hS patterns epsilon hepsilon


-- created on 2026-10-23
