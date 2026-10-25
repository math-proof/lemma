import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.FreeCurrentFamilyMixing
open MeasureTheory Set StatMech StatMech.FrontierB


/--
[infiniteFreeCurrentMeasure_singleton_real_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeCurrentFamilyMixing.lean)
-/
@[path]
private lemma infiniteFreeCurrentMeasure_singleton_real_eq_eq
  {d : Nat}
  {beta : Real}
  {S : Finset (Sym2 (Site d))}
-- given
  (hbeta : 0 < beta)
  (hS : (↑S : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet)
  (a : ↑S -> Nat) :
-- imply
  (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real (currentCylinder S {a}) = (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real (currentParityPatternCylinder S (currentLocalParity a)) * ENNReal.toReal (finiteParityPMF S beta hbeta (currentLocalParity a) a) := by
-- proof
  apply StatMech.FrontierB.infiniteFreeCurrentMeasure_singleton_real_eq hbeta S hS a

/--
[infiniteFreeCurrentMeasure_singleton_inter_shift_real_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeCurrentFamilyMixing.lean)
-/
@[path]
private lemma infiniteFreeCurrentMeasure_singleton_inter_shift_real_eq_eq
  {d : Nat}
  {beta : Real}
  {g : Multiplicative (Site d)}
  {S T : Finset (Sym2 (Site d))}
-- given
  (hbeta : 0 < beta)
  (hS : (↑S : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet)
  (hT : (↑T : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet)
  (hdisj : Disjoint S (currentShiftFinset g T))
  (a : ↑S -> Nat)
  (b : ↑T -> Nat) :
-- imply
  (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real (currentCylinder S {a} ∩ (currentShift g) ⁻¹' currentCylinder T {b}) = (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real (currentParityPatternCylinder S (currentLocalParity a) ∩ (currentShift g) ⁻¹' currentParityPatternCylinder T (currentLocalParity b)) * (ENNReal.toReal (finiteParityPMF S beta hbeta (currentLocalParity a) a) * ENNReal.toReal (finiteParityPMF T beta hbeta (currentLocalParity b) b)) := by
-- proof
  apply StatMech.FrontierB.infiniteFreeCurrentMeasure_singleton_inter_shift_real_eq hbeta g S T hS hT hdisj a b

/--
[infiniteFreeCurrentMeasure_singleton_family_pairMixing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeCurrentFamilyMixing.lean)
-/
@[path]
private lemma infiniteFreeCurrentMeasure_singleton_family_pairMixing_eq
  {d : Nat}
  {beta : Real}
  {S : Finset (Sym2 (Site d))}
  {epsilon : Real}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta)
  (hS : (↑S : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet)
  (patterns : Finset (↑S -> Nat))
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ g : Multiplicative (Site d), Disjoint S (currentShiftFinset g S) ∧ ∀ a ∈ patterns, ∀ b ∈ patterns, abs ((infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real (currentCylinder S {a} ∩ (currentShift g) ⁻¹' currentCylinder S {b}) - (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real (currentCylinder S {a}) * (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real (currentCylinder S {b})) < epsilon := by
-- proof
  apply StatMech.FrontierB.infiniteFreeCurrentMeasure_singleton_family_pairMixing hd hbeta S hS patterns epsilon hepsilon

/--
[infiniteFreeCurrentMeasure_latticeCylinder_family_pairMixing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeCurrentFamilyMixing.lean)
-/
@[path]
private lemma infiniteFreeCurrentMeasure_latticeCylinder_family_pairMixing_eq
  {d : Nat}
  {beta : Real}
  {S : Finset (Sym2 (Site d))}
  {epsilon : Real}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta)
  (hS : (↑S : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet)
  (accepted : Finset (Set (↑S -> Nat)))
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ g : Multiplicative (Site d), ∀ A ∈ accepted, ∀ B ∈ accepted, abs ((infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real (currentCylinder S A ∩ (currentShift g) ⁻¹' currentCylinder S B) - (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real (currentCylinder S A) * (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real (currentCylinder S B)) < epsilon := by
-- proof
  apply StatMech.FrontierB.infiniteFreeCurrentMeasure_latticeCylinder_family_pairMixing hd hbeta S hS accepted epsilon hepsilon

/--
[infiniteFreeCurrentMeasure_cylinderPairMixing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeCurrentFamilyMixing.lean)
-/
@[path]
private lemma infiniteFreeCurrentMeasure_cylinderPairMixing_eq
  {d : Nat}
  {beta : Real}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta) :
-- imply
  CurrentCylinderPairMixing (H := Multiplicative (Site d)) (infiniteFreeCurrentMeasure d beta hbeta.le : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FrontierB.infiniteFreeCurrentMeasure_cylinderPairMixing hd hbeta

/--
[infiniteFreeCurrentMeasure_isErgodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeCurrentFamilyMixing.lean)
-/
@[path]
private lemma infiniteFreeCurrentMeasure_isErgodic_eq
  {d : Nat}
  {beta : Real}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta) :
-- imply
  CurrentIsErgodic (H := Multiplicative (Site d)) (infiniteFreeCurrentMeasure d beta hbeta.le : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FrontierB.infiniteFreeCurrentMeasure_isErgodic hd hbeta


-- created on 2026-10-23
