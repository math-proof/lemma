import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.PlusAxisMixing
open Filter MeasureTheory Set Topology StatMech StatMech.FrontierB


/--
[plusState_multiOpen_upper_of_outside_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusAxisMixing.lean)
-/
@[path]
private lemma plusState_multiOpen_upper_of_outside_box_eq
  {d : Nat}
  {d N : Nat}
  {beta : Real}
  {g : Multiplicative (Site d)}
  {T U : Finset (Site d)}
-- given
  (hbeta : 0 ≤ beta)
  (houtside : ∀ x ∈ U.image (fun y => g⁻¹ • y), x ∉ box d N) :
-- imply
  let mu := (plusState d beta 0 : Measure (ConfigSpace (Site d))) mu.real (fmu_multiOpen T ∩ (shift g) ⁻¹' fmu_multiOpen U) ≤ (plusMeasure d N beta 0 : Measure (ConfigSpace (Site d))).real (fmu_multiOpen T) * mu.real (fmu_multiOpen U) := by
-- proof
  apply StatMech.FrontierB.plusState_multiOpen_upper_of_outside_box d N hbeta g T U houtside

/--
[plusState_multiOpen_axis_pairCorrelation_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusAxisMixing.lean)
-/
@[path]
private lemma plusState_multiOpen_axis_pairCorrelation_tendsto_eq
  {d : Nat}
  {beta : Real}
  {T U : Finset (Site d)}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 ≤ beta) :
-- imply
  let mu := (plusState d beta 0 : Measure (ConfigSpace (Site d))) Tendsto (fun k : Nat => mu.real (fmu_multiOpen T ∩ (shift (FK.freeAxisTranslationPower hd k)) ⁻¹' fmu_multiOpen U)) atTop (nhds (mu.real (fmu_multiOpen T) * mu.real (fmu_multiOpen U))) := by
-- proof
  apply StatMech.FrontierB.plusState_multiOpen_axis_pairCorrelation_tendsto hd hbeta T U

/--
[plusState_moInd_axis_pairCorrelation_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusAxisMixing.lean)
-/
@[path]
private lemma plusState_moInd_axis_pairCorrelation_tendsto_eq
  {d : Nat}
  {beta : Real}
  {T U : Finset (Site d)}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 ≤ beta) :
-- imply
  let mu := (plusState d beta 0 : Measure (ConfigSpace (Site d))) Tendsto (fun k : Nat => ∫ omega, fmu_moInd T omega * fmu_moInd U (shift (FK.freeAxisTranslationPower hd k) omega) ∂mu) atTop (nhds (mu.real (fmu_multiOpen T) * mu.real (fmu_multiOpen U))) := by
-- proof
  apply StatMech.FrontierB.plusState_moInd_axis_pairCorrelation_tendsto hd hbeta T U

/--
[currentShiftFinset_axis_eventually_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusAxisMixing.lean)
-/
@[path]
private lemma currentShiftFinset_axis_eventually_disjoint_eq
  {d : Nat}
  {S T : Finset (Sym2 (Site d))}
-- given
  (hd : 1 ≤ d) :
-- imply
  ∀ᶠ k in atTop, Disjoint S (currentShiftFinset (FK.freeAxisTranslationPower hd k) T) := by
-- proof
  apply StatMech.FrontierB.currentShiftFinset_axis_eventually_disjoint hd S T

/--
[infinitePlusCurrentMeasure_parityPattern_axis_pairCorrelation_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusAxisMixing.lean)
-/
@[path]
private lemma infinitePlusCurrentMeasure_parityPattern_axis_pairCorrelation_tendsto_eq
  {d : Nat}
  {beta : Real}
  {S T : Finset (Sym2 (Site d))}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta)
  (hS : (↑S : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet)
  (hT : (↑T : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet)
  (odd : ↑S -> Bool)
  (odd' : ↑T -> Bool) :
-- imply
  let nu := (infinitePlusCurrentMeasure d beta hbeta.le : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) Tendsto (fun k : Nat => nu.real (currentParityPatternCylinder S odd ∩ (currentShift (FK.freeAxisTranslationPower hd k)) ⁻¹' currentParityPatternCylinder T odd')) atTop (nhds (nu.real (currentParityPatternCylinder S odd) * nu.real (currentParityPatternCylinder T odd'))) := by
-- proof
  apply StatMech.FrontierB.infinitePlusCurrentMeasure_parityPattern_axis_pairCorrelation_tendsto hd hbeta S T hS hT odd odd'

/--
[infinitePlusCurrentMeasure_singleton_axis_pairCorrelation_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusAxisMixing.lean)
-/
@[path]
private lemma infinitePlusCurrentMeasure_singleton_axis_pairCorrelation_tendsto_eq
  {d : Nat}
  {beta : Real}
  {S T : Finset (Sym2 (Site d))}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta)
  (hS : (↑S : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet)
  (hT : (↑T : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet)
  (a : ↑S -> Nat)
  (b : ↑T -> Nat) :
-- imply
  let nu := (infinitePlusCurrentMeasure d beta hbeta.le : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) Tendsto (fun k : Nat => nu.real (currentCylinder S {a} ∩ (currentShift (FK.freeAxisTranslationPower hd k)) ⁻¹' currentCylinder T {b})) atTop (nhds (nu.real (currentCylinder S {a}) * nu.real (currentCylinder T {b}))) := by
-- proof
  apply StatMech.FrontierB.infinitePlusCurrentMeasure_singleton_axis_pairCorrelation_tendsto hd hbeta S T hS hT a b

/--
[infinitePlusCurrentMeasure_finsetCylinder_axis_pairCorrelation_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusAxisMixing.lean)
-/
@[path]
private lemma infinitePlusCurrentMeasure_finsetCylinder_axis_pairCorrelation_tendsto_eq
  {d : Nat}
  {beta : Real}
  {S : Finset (Sym2 (Site d))}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta)
  (hS : (↑S : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet)
  (P Q : Finset (↑S -> Nat)) :
-- imply
  let nu := (infinitePlusCurrentMeasure d beta hbeta.le : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) Tendsto (fun k : Nat => nu.real (currentCylinder S (↑P : Set (↑S -> Nat)) ∩ (currentShift (FK.freeAxisTranslationPower hd k)) ⁻¹' currentCylinder S (↑Q : Set (↑S -> Nat)))) atTop (nhds (nu.real (currentCylinder S (↑P : Set (↑S -> Nat))) * nu.real (currentCylinder S (↑Q : Set (↑S -> Nat))))) := by
-- proof
  apply StatMech.FrontierB.infinitePlusCurrentMeasure_finsetCylinder_axis_pairCorrelation_tendsto hd hbeta S hS P Q

/--
[infinitePlusCurrentMeasure_latticeCylinder_axis_pairCorrelation_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusAxisMixing.lean)
-/
@[path]
private lemma infinitePlusCurrentMeasure_latticeCylinder_axis_pairCorrelation_tendsto_eq
  {d : Nat}
  {beta : Real}
  {S : Finset (Sym2 (Site d))}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta)
  (hS : (↑S : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet)
  (A B : Set (↑S -> Nat)) :
-- imply
  let nu := (infinitePlusCurrentMeasure d beta hbeta.le : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) Tendsto (fun k : Nat => nu.real (currentCylinder S A ∩ (currentShift (FK.freeAxisTranslationPower hd k)) ⁻¹' currentCylinder S B)) atTop (nhds (nu.real (currentCylinder S A) * nu.real (currentCylinder S B))) := by
-- proof
  apply StatMech.FrontierB.infinitePlusCurrentMeasure_latticeCylinder_axis_pairCorrelation_tendsto hd hbeta S hS A B

/--
[infinitePlusCurrentMeasure_cylinder_axis_pairCorrelation_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusAxisMixing.lean)
-/
@[path]
private lemma infinitePlusCurrentMeasure_cylinder_axis_pairCorrelation_tendsto_eq
  {d : Nat}
  {beta : Real}
  {C D : Set (InfiniteCurrentConfig (Sym2 (Site d)))}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta)
  (hC : C ∈ measurableCylinders (fun _ : Sym2 (Site d) => Nat))
  (hD : D ∈ measurableCylinders (fun _ : Sym2 (Site d) => Nat)) :
-- imply
  let nu := (infinitePlusCurrentMeasure d beta hbeta.le : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) Tendsto (fun k : Nat => nu.real (C ∩ (currentShift (FK.freeAxisTranslationPower hd k)) ⁻¹' D)) atTop (nhds (nu.real C * nu.real D)) := by
-- proof
  apply StatMech.FrontierB.infinitePlusCurrentMeasure_cylinder_axis_pairCorrelation_tendsto hd hbeta C D hC hD


-- created on 2026-10-23
