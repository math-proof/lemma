import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierB.PlusCurrentSingletonMixing
open MeasureTheory Set StatMech StatMech.FrontierB


/--
[mergeLocalPattern_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusCurrentSingletonMixing.lean)
-/
@[path]
private lemma mergeLocalPattern_left_eq
  [DecidableEq E]
  {S T : Finset E}
  {e : E}
-- given
  (hdisj : Disjoint S T)
  (a : ↑S -> A)
  (b : ↑T -> A)
  (he : e ∈ S) :
-- imply
  mergeLocalPattern S T hdisj a b ⟨e, Finset.mem_union_left T he⟩ = a ⟨e, he⟩ := by
-- proof
  apply StatMech.FrontierB.mergeLocalPattern_left S T hdisj a b e he

/--
[mergeLocalPattern_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusCurrentSingletonMixing.lean)
-/
@[path]
private lemma mergeLocalPattern_right_eq
  [DecidableEq E]
  {S T : Finset E}
  {e : E}
-- given
  (hdisj : Disjoint S T)
  (a : ↑S -> A)
  (b : ↑T -> A)
  (he : e ∈ T) :
-- imply
  mergeLocalPattern S T hdisj a b ⟨e, Finset.mem_union_right S he⟩ = b ⟨e, he⟩ := by
-- proof
  apply StatMech.FrontierB.mergeLocalPattern_right S T hdisj a b e he

/--
[finiteParityKernel_merge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusCurrentSingletonMixing.lean)
-/
@[path]
private lemma finiteParityKernel_merge_eq
  [DecidableEq E]
  {S T : Finset E}
  {beta : Real}
-- given
  (hdisj : Disjoint S T)
  (odd : ↑S -> Bool)
  (odd' : ↑T -> Bool)
  (a : ↑S -> Nat)
  (b : ↑T -> Nat) :
-- imply
  finiteParityKernel (S ∪ T) beta (mergeLocalPattern S T hdisj odd odd') (mergeLocalPattern S T hdisj a b) = finiteParityKernel S beta odd a * finiteParityKernel T beta odd' b := by
-- proof
  apply StatMech.FrontierB.finiteParityKernel_merge S T hdisj beta odd odd' a b

/--
[finiteParityPMF_merge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusCurrentSingletonMixing.lean)
-/
@[path]
private lemma finiteParityPMF_merge_eq
  [DecidableEq E]
  {S T : Finset E}
  {beta : Real}
-- given
  (hdisj : Disjoint S T)
  (hbeta : 0 < beta)
  (odd : ↑S -> Bool)
  (odd' : ↑T -> Bool)
  (a : ↑S -> Nat)
  (b : ↑T -> Nat) :
-- imply
  finiteParityPMF (S ∪ T) beta hbeta (mergeLocalPattern S T hdisj odd odd') (mergeLocalPattern S T hdisj a b) = finiteParityPMF S beta hbeta odd a * finiteParityPMF T beta hbeta odd' b := by
-- proof
  apply StatMech.FrontierB.finiteParityPMF_merge S T hdisj beta hbeta odd odd' a b

/--
[currentLocalParity_merge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusCurrentSingletonMixing.lean)
-/
@[path]
private lemma currentLocalParity_merge_eq
  [DecidableEq E]
  {S T : Finset E}
-- given
  (hdisj : Disjoint S T)
  (a : ↑S -> Nat)
  (b : ↑T -> Nat) :
-- imply
  currentLocalParity (mergeLocalPattern S T hdisj a b) = mergeLocalPattern S T hdisj (currentLocalParity a) (currentLocalParity b) := by
-- proof
  apply StatMech.FrontierB.currentLocalParity_merge S T hdisj a b

/--
[currentCylinder_singleton_inter_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusCurrentSingletonMixing.lean)
-/
@[path]
private lemma currentCylinder_singleton_inter_of_disjoint_eq
  [DecidableEq E]
  {S T : Finset E}
-- given
  (hdisj : Disjoint S T)
  (a : ↑S -> Nat)
  (b : ↑T -> Nat) :
-- imply
  currentCylinder S {a} ∩ currentCylinder T {b} = currentCylinder (S ∪ T) {mergeLocalPattern S T hdisj a b} := by
-- proof
  apply StatMech.FrontierB.currentCylinder_singleton_inter_of_disjoint S T hdisj a b

/--
[currentParityPatternCylinder_inter_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusCurrentSingletonMixing.lean)
-/
@[path]
private lemma currentParityPatternCylinder_inter_of_disjoint_eq
  [DecidableEq E]
  {S T : Finset E}
-- given
  (hdisj : Disjoint S T)
  (odd : ↑S -> Bool)
  (odd' : ↑T -> Bool) :
-- imply
  currentParityPatternCylinder S odd ∩ currentParityPatternCylinder T odd' = currentParityPatternCylinder (S ∪ T) (mergeLocalPattern S T hdisj odd odd') := by
-- proof
  apply StatMech.FrontierB.currentParityPatternCylinder_inter_of_disjoint S T hdisj odd odd'

/--
[currentCylinder_singleton_inter_shift_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusCurrentSingletonMixing.lean)
-/
@[path]
private lemma currentCylinder_singleton_inter_shift_of_disjoint_eq
  [DecidableEq E]
  [Group H]
  [MulAction H E]
  {g : H}
  {S T : Finset E}
-- given
  (hdisj : Disjoint S (currentShiftFinset g T))
  (a : ↑S -> Nat)
  (b : ↑T -> Nat) :
-- imply
  currentCylinder S {a} ∩ (currentShift g) ⁻¹' currentCylinder T {b} = currentCylinder (S ∪ currentShiftFinset g T) {mergeLocalPattern S (currentShiftFinset g T) hdisj a (currentShiftPattern g T b)} := by
-- proof
  apply StatMech.FrontierB.currentCylinder_singleton_inter_shift_of_disjoint g S T hdisj a b

/--
[currentParityPatternCylinder_inter_shift_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusCurrentSingletonMixing.lean)
-/
@[path]
private lemma currentParityPatternCylinder_inter_shift_of_disjoint_eq
  [DecidableEq E]
  [Group H]
  [MulAction H E]
  {g : H}
  {S T : Finset E}
-- given
  (hdisj : Disjoint S (currentShiftFinset g T))
  (odd : ↑S -> Bool)
  (odd' : ↑T -> Bool) :
-- imply
  currentParityPatternCylinder S odd ∩ (currentShift g) ⁻¹' currentParityPatternCylinder T odd' = currentParityPatternCylinder (S ∪ currentShiftFinset g T) (mergeLocalPattern S (currentShiftFinset g T) hdisj odd (currentShiftPattern g T odd')) := by
-- proof
  apply StatMech.FrontierB.currentParityPatternCylinder_inter_shift_of_disjoint g S T hdisj odd odd'

/--
[infinitePlusCurrentMeasure_singleton_real_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusCurrentSingletonMixing.lean)
-/
@[path]
private lemma infinitePlusCurrentMeasure_singleton_real_eq_eq
  {d : Nat}
  {beta : Real}
  {S : Finset (Sym2 (Site d))}
-- given
  (hbeta : 0 < beta)
  (hS : (↑S : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet)
  (a : ↑S -> Nat) :
-- imply
  (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real (currentCylinder S {a}) = (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real (currentParityPatternCylinder S (currentLocalParity a)) * ENNReal.toReal (finiteParityPMF S beta hbeta (currentLocalParity a) a) := by
-- proof
  apply StatMech.FrontierB.infinitePlusCurrentMeasure_singleton_real_eq hbeta S hS a

/--
[infinitePlusCurrentMeasure_singleton_inter_shift_real_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusCurrentSingletonMixing.lean)
-/
@[path]
private lemma infinitePlusCurrentMeasure_singleton_inter_shift_real_eq_eq
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
  (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real (currentCylinder S {a} ∩ (currentShift g) ⁻¹' currentCylinder T {b}) = (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real (currentParityPatternCylinder S (currentLocalParity a) ∩ (currentShift g) ⁻¹' currentParityPatternCylinder T (currentLocalParity b)) * (ENNReal.toReal (finiteParityPMF S beta hbeta (currentLocalParity a) a) * ENNReal.toReal (finiteParityPMF T beta hbeta (currentLocalParity b) b)) := by
-- proof
  apply StatMech.FrontierB.infinitePlusCurrentMeasure_singleton_inter_shift_real_eq hbeta g S T hS hT hdisj a b

/--
[infinitePlusCurrentMeasure_singleton_pairMixing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusCurrentSingletonMixing.lean)
-/
@[path]
private lemma infinitePlusCurrentMeasure_singleton_pairMixing_eq
  {d : Nat}
  {beta : Real}
  {S T : Finset (Sym2 (Site d))}
  {epsilon : Real}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta)
  (hS : (↑S : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet)
  (hT : (↑T : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet)
  (a : ↑S -> Nat)
  (b : ↑T -> Nat)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ g : Multiplicative (Site d), Disjoint S (currentShiftFinset g T) ∧ abs ((infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real (currentCylinder S {a} ∩ (currentShift g) ⁻¹' currentCylinder T {b}) - (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real (currentCylinder S {a}) * (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real (currentCylinder T {b})) < epsilon := by
-- proof
  apply StatMech.FrontierB.infinitePlusCurrentMeasure_singleton_pairMixing hd hbeta S T hS hT a b epsilon hepsilon


-- created on 2026-10-23
