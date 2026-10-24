import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierB.PlusCurrentFamilyMixing
open MeasureTheory Set StatMech StatMech.FrontierB


/--
[infinitePlusCurrentMeasure_parityPattern_family_pairMixing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusCurrentFamilyMixing.lean)
-/
@[path]
private lemma infinitePlusCurrentMeasure_parityPattern_family_pairMixing_eq
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
  ∃ g : Multiplicative (Site d), Disjoint S (currentShiftFinset g S) ∧ ∀ odd ∈ patterns, ∀ odd' ∈ patterns, abs ((infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real (currentParityPatternCylinder S odd ∩ (currentShift g) ⁻¹' currentParityPatternCylinder S odd') - (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real (currentParityPatternCylinder S odd) * (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real (currentParityPatternCylinder S odd')) < epsilon := by
-- proof
  apply StatMech.FrontierB.infinitePlusCurrentMeasure_parityPattern_family_pairMixing hd hbeta S hS patterns epsilon hepsilon

/--
[infinitePlusCurrentMeasure_singleton_family_pairMixing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusCurrentFamilyMixing.lean)
-/
@[path]
private lemma infinitePlusCurrentMeasure_singleton_family_pairMixing_eq
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
  ∃ g : Multiplicative (Site d), Disjoint S (currentShiftFinset g S) ∧ ∀ a ∈ patterns, ∀ b ∈ patterns, abs ((infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real (currentCylinder S {a} ∩ (currentShift g) ⁻¹' currentCylinder S {b}) - (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real (currentCylinder S {a}) * (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real (currentCylinder S {b})) < epsilon := by
-- proof
  apply StatMech.FrontierB.infinitePlusCurrentMeasure_singleton_family_pairMixing hd hbeta S hS patterns epsilon hepsilon

/--
[pmf_exists_finset_compl_toReal_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusCurrentFamilyMixing.lean)
-/
@[path]
private lemma pmf_exists_finset_compl_toReal_lt_eq
  [Countable A]
  [MeasurableSpace A]
  [MeasurableSingletonClass A]
  {p : PMF A}
  {epsilon : Real}
-- given
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ K : Finset A, ENNReal.toReal (p.toMeasure (↑K : Set A)ᶜ) < epsilon := by
-- proof
  apply StatMech.FrontierB.pmf_exists_finset_compl_toReal_lt p epsilon hepsilon

/--
[currentCylinder_finset_real_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusCurrentFamilyMixing.lean)
-/
@[path]
private lemma currentCylinder_finset_real_eq_sum_eq
  [Countable E]
  {mu : Measure (InfiniteCurrentConfig E)}
  [IsFiniteMeasure mu]
  {S : Finset E}
-- given
  (P : Finset (↑S -> Nat)) :
-- imply
  mu.real (currentCylinder S (↑P : Set (↑S -> Nat))) = ∑ a ∈ P, mu.real (currentCylinder S {a}) := by
-- proof
  apply StatMech.FrontierB.currentCylinder_finset_real_eq_sum mu S P

/--
[currentCylinder_finset_inter_shift_real_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusCurrentFamilyMixing.lean)
-/
@[path]
private lemma currentCylinder_finset_inter_shift_real_eq_sum_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {mu : Measure (InfiniteCurrentConfig E)}
  [IsFiniteMeasure mu]
  {g : H}
  {S : Finset E}
-- given
  (P Q : Finset (↑S -> Nat)) :
-- imply
  mu.real (currentCylinder S (↑P : Set (↑S -> Nat)) ∩ (currentShift g) ⁻¹' currentCylinder S (↑Q : Set (↑S -> Nat))) = ∑ a ∈ P, ∑ b ∈ Q, mu.real (currentCylinder S {a} ∩ (currentShift g) ⁻¹' currentCylinder S {b}) := by
-- proof
  apply StatMech.FrontierB.currentCylinder_finset_inter_shift_real_eq_sum mu g S P Q

/--
[infinitePlusCurrentMeasure_latticeCylinder_family_pairMixing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusCurrentFamilyMixing.lean)
-/
@[path]
private lemma infinitePlusCurrentMeasure_latticeCylinder_family_pairMixing_eq
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
  ∃ g : Multiplicative (Site d), ∀ A ∈ accepted, ∀ B ∈ accepted, abs ((infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real (currentCylinder S A ∩ (currentShift g) ⁻¹' currentCylinder S B) - (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real (currentCylinder S A) * (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real (currentCylinder S B)) < epsilon := by
-- proof
  apply StatMech.FrontierB.infinitePlusCurrentMeasure_latticeCylinder_family_pairMixing hd hbeta S hS accepted epsilon hepsilon

/--
[restrictCurrent_eq_extendLatticeLocalPattern](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusCurrentFamilyMixing.lean)
-/
@[path]
private lemma restrictCurrent_eq_extendLatticeLocalPattern_eq
  {d : Nat}
  {S : Finset (Sym2 (Site d))}
  {m : InfiniteCurrentConfig (Sym2 (Site d))}
-- given
  (hm : ∀ e ∈ S, e ∉ (hypercubicLattice d).edgeSet -> m e = 0) :
-- imply
  restrictCurrent S m = extendLatticeLocalPattern d S (restrictCurrent (latticeEdgePart d S) m) := by
-- proof
  apply StatMech.FrontierB.restrictCurrent_eq_extendLatticeLocalPattern d S m hm

/--
[currentCylinder_ae_eq_latticeReduction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusCurrentFamilyMixing.lean)
-/
@[path]
private lemma currentCylinder_ae_eq_latticeReduction_eq
  {d : Nat}
  {mu : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
  {S : Finset (Sym2 (Site d))}
-- given
  (hzero : ∀ e, e ∉ (hypercubicLattice d).edgeSet -> (mu : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) {m | m e = 0} = 1)
  (A : Set (↑S -> Nat)) :
-- imply
  (fun m => m ∈ currentCylinder S A) =ᵐ[(mu : Measure _)] (fun m => m ∈ currentCylinder (latticeEdgePart d S) (latticeReducedPatternSet d S A)) := by
-- proof
  apply StatMech.FrontierB.currentCylinder_ae_eq_latticeReduction d mu S hzero A

/--
[currentCylinder_liftCurrentPatternSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusCurrentFamilyMixing.lean)
-/
@[path]
private lemma currentCylinder_liftCurrentPatternSet_eq
  {S U : Finset E}
-- given
  (hSU : S ⊆ U)
  (A : Set (↑S -> Nat)) :
-- imply
  currentCylinder U (liftCurrentPatternSet hSU A) = currentCylinder S A := by
-- proof
  apply StatMech.FrontierB.currentCylinder_liftCurrentPatternSet hSU A

/--
[infinitePlusCurrentMeasure_cylinderPairMixing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusCurrentFamilyMixing.lean)
-/
@[path]
private lemma infinitePlusCurrentMeasure_cylinderPairMixing_eq
  {d : Nat}
  {beta : Real}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta) :
-- imply
  CurrentCylinderPairMixing (H := Multiplicative (Site d)) (infinitePlusCurrentMeasure d beta hbeta.le : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FrontierB.infinitePlusCurrentMeasure_cylinderPairMixing hd hbeta

/--
[infinitePlusCurrentMeasure_isErgodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusCurrentFamilyMixing.lean)
-/
@[path]
private lemma infinitePlusCurrentMeasure_isErgodic_eq
  {d : Nat}
  {beta : Real}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta) :
-- imply
  CurrentIsErgodic (H := Multiplicative (Site d)) (infinitePlusCurrentMeasure d beta hbeta.le : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FrontierB.infinitePlusCurrentMeasure_isErgodic hd hbeta


-- created on 2026-10-23
