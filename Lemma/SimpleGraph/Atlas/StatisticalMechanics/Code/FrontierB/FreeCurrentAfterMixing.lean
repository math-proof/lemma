import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierB.FreeCurrentAfterMixing
open MeasureTheory Set StatMech StatMech.FrontierB


/--
[infiniteFreeCurrentMeasure_singleton_family_pairMixing_after](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeCurrentAfterMixing.lean)
-/
@[path]
private lemma infiniteFreeCurrentMeasure_singleton_family_pairMixing_after_eq
  {d : Nat}
  {beta : Real}
  {K0 : Nat}
  {S : Finset (Sym2 (Site d))}
  {patterns : Finset (↑S → Nat)}
  {epsilon : Real}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta)
  (hS : (↑S : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ k : Nat, K0 ≤ k ∧ Disjoint S (currentShiftFinset (FK.freeAxisTranslationPower hd k) S) ∧ ∀ a ∈ patterns, ∀ b ∈ patterns, abs ((infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real (currentCylinder S {a} ∩ (currentShift (FK.freeAxisTranslationPower hd k)) ⁻¹' currentCylinder S {b}) - (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real (currentCylinder S {a}) * (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real (currentCylinder S {b})) < epsilon := by
-- proof
  apply StatMech.FrontierB.infiniteFreeCurrentMeasure_singleton_family_pairMixing_after hd hbeta K0 S hS patterns epsilon hepsilon

/--
[current_pairGap_lt_of_approx](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeCurrentAfterMixing.lean)
-/
@[path]
private lemma current_pairGap_lt_of_approx_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {mu : Measure (InfiniteCurrentConfig E)}
  [IsProbabilityMeasure mu]
  {g : H}
  {A A0 B B0 : Set (InfiniteCurrentConfig E)}
  {eta delta : Real}
-- given
  (hti : CurrentIsTranslationInvariant (H := H) mu)
  (hA : MeasurableSet A)
  (hA0 : MeasurableSet A0)
  (hB : MeasurableSet B)
  (hB0 : MeasurableSet B0)
  (hAapprox : mu.real (A ∆ A0) < eta)
  (hBapprox : mu.real (B ∆ B0) < eta)
  (hfinite : abs (mu.real (A0 ∩ (currentShift g) ⁻¹' B0) - mu.real A0 * mu.real B0) < delta) :
-- imply
  abs (mu.real (A ∩ (currentShift g) ⁻¹' B) - mu.real A * mu.real B) < 4 * eta + delta := by
-- proof
  apply StatMech.FrontierB.current_pairGap_lt_of_approx mu hti g hA hA0 hB hB0 hAapprox hBapprox hfinite

/--
[infiniteFreeCurrentMeasure_latticeCylinder_family_pairMixing_after](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeCurrentAfterMixing.lean)
-/
@[path]
private lemma infiniteFreeCurrentMeasure_latticeCylinder_family_pairMixing_after_eq
  {d : Nat}
  {beta : Real}
  {K0 : Nat}
  {S : Finset (Sym2 (Site d))}
  {accepted : Finset (Set (↑S → Nat))}
  {epsilon : Real}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta)
  (hS : (↑S : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ k : Nat, K0 ≤ k ∧ ∀ A ∈ accepted, ∀ B ∈ accepted, abs ((infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real (currentCylinder S A ∩ (currentShift (FK.freeAxisTranslationPower hd k)) ⁻¹' currentCylinder S B) - (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real (currentCylinder S A) * (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real (currentCylinder S B)) < epsilon := by
-- proof
  apply StatMech.FrontierB.infiniteFreeCurrentMeasure_latticeCylinder_family_pairMixing_after hd hbeta K0 S hS accepted epsilon hepsilon

/--
[infiniteFreeCurrentMeasure_cylinderPairMixing_after](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeCurrentAfterMixing.lean)
-/
@[path]
private lemma infiniteFreeCurrentMeasure_cylinderPairMixing_after_eq
  {d : Nat}
  {beta : Real}
  {K0 : Nat}
  {family : Finset (Set (InfiniteCurrentConfig (Sym2 (Site d))))}
  {epsilon : Real}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta)
  (hfamily : ∀ A ∈ family, A ∈ measurableCylinders (fun _ : Sym2 (Site d) => Nat))
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ k : Nat, K0 ≤ k ∧ ∀ A ∈ family, ∀ B ∈ family, abs ((infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real (A ∩ (currentShift (FK.freeAxisTranslationPower hd k)) ⁻¹' B) - (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real A * (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real B) < epsilon := by
-- proof
  apply StatMech.FrontierB.infiniteFreeCurrentMeasure_cylinderPairMixing_after hd hbeta K0 family hfamily epsilon hepsilon


-- created on 2026-10-23
