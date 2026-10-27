import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentSelectionIndependence.Part3
open MeasureTheory Filter Topology StatMech StatMech.FrontierB


/--
[currentParityMarginalPMF_toMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSelectionIndependence.lean)
-/
@[path]
private lemma currentParityMarginalPMF_toMeasure_eq
  [Countable E]
  [DecidableEq E]
  {mu : ProbabilityMeasure (InfiniteCurrentConfig E)}
  {S : Finset E} :
-- imply
  (currentParityMarginalPMF mu S).toMeasure = (((currentMarginal mu S).map (Measurable.of_discrete (f := currentLocalParity)).aemeasurable : ProbabilityMeasure (↑S → Bool)) : Measure (↑S → Bool)) := by
-- proof
  apply StatMech.FrontierB.currentParityMarginalPMF_toMeasure mu S

/--
[preimage_boolAvoid_currentLocalParity_restrictCurrent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSelectionIndependence.lean)
-/
@[path]
private lemma preimage_boolAvoid_currentLocalParity_restrictCurrent_eq
  [DecidableEq E]
  {S : Finset E}
  {T : Finset ↑S} :
-- imply
  (currentLocalParity ∘ restrictCurrent S) ⁻¹' boolAvoid T = currentParityAvoidCylinder (ambientSubfinset S T) := by
-- proof
  apply StatMech.FrontierB.preimage_boolAvoid_currentLocalParity_restrictCurrent S T

/--
[currentParityMarginalPMF_avoid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSelectionIndependence.lean)
-/
@[path]
private lemma currentParityMarginalPMF_avoid_eq
  [Countable E]
  [DecidableEq E]
  {mu : ProbabilityMeasure (InfiniteCurrentConfig E)}
  {S : Finset E}
  {T : Finset ↑S} :
-- imply
  (currentParityMarginalPMF mu S).toMeasure (boolAvoid T) = (mu : Measure (InfiniteCurrentConfig E)) (currentParityAvoidCylinder (ambientSubfinset S T)) := by
-- proof
  apply StatMech.FrontierB.currentParityMarginalPMF_avoid mu S T

/--
[currentParityMarginalPMF_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSelectionIndependence.lean)
-/
@[path]
private lemma currentParityMarginalPMF_apply_eq
  [Countable E]
  [DecidableEq E]
  {mu : ProbabilityMeasure (InfiniteCurrentConfig E)}
  {S : Finset E}
  {odd : ↑S → Bool} :
-- imply
  currentParityMarginalPMF mu S odd = (mu : Measure (InfiniteCurrentConfig E)) (currentParityPatternCylinder S odd) := by
-- proof
  apply StatMech.FrontierB.currentParityMarginalPMF_apply mu S odd

/--
[WeakCurrentConverges.cylinderENNReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSelectionIndependence.lean)
-/
@[path]
private lemma cylinderENNReal_eq
  [Countable E]
  {mu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E)}
  {nu : ProbabilityMeasure (InfiniteCurrentConfig E)}
  {S : Finset E}
  {A : Set (↑S → ℕ)}
-- given
  (h : WeakCurrentConverges mu nu) :
-- imply
  Tendsto (fun k => (mu k : Measure (InfiniteCurrentConfig E)) (currentCylinder S A)) atTop (nhds ((nu : Measure (InfiniteCurrentConfig E)) (currentCylinder S A))) := by
-- proof
  apply StatMech.FrontierB.WeakCurrentConverges.cylinderENNReal h S A

/--
[currentParityAvoidCylinder_eq_currentCylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSelectionIndependence.lean)
-/
@[path]
private lemma currentParityAvoidCylinder_eq_currentCylinder_eq
  {S : Finset E} :
-- imply
  currentParityAvoidCylinder S = currentCylinder S {a | ∀ i, Even (a i)} := by
-- proof
  apply StatMech.FrontierB.currentParityAvoidCylinder_eq_currentCylinder S

/--
[currentLimit_parityMarginal_eq_of_avoid_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSelectionIndependence.lean)
-/
@[path]
private lemma currentLimit_parityMarginal_eq_of_avoid_tendsto_eq
  [Countable E]
  [DecidableEq E]
  {mu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E)}
  {S : Finset E}
  {nu rho : ProbabilityMeasure (InfiniteCurrentConfig E)}
  {phi psi : ℕ → ℕ}
-- given
  (havoid : ∀ A : Finset E, ∃ L : ℝ≥0∞, Tendsto (fun n => (mu n : Measure (InfiniteCurrentConfig E)) (currentParityAvoidCylinder A)) atTop (nhds L))
  (hphi : StrictMono phi)
  (hpsi : StrictMono psi)
  (hnu : WeakCurrentConverges (mu ∘ phi) nu)
  (hrho : WeakCurrentConverges (mu ∘ psi) rho) :
-- imply
  currentParityMarginalPMF nu S = currentParityMarginalPMF rho S := by
-- proof
  apply StatMech.FrontierB.currentLimit_parityMarginal_eq_of_avoid_tendsto mu havoid S hphi hpsi hnu hrho

/--
[currentMarginal_eq_of_parityMarginal_eq_of_pattern_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSelectionIndependence.lean)
-/
@[path]
private lemma currentMarginal_eq_of_parityMarginal_eq_of_pattern_factor_eq
  [Countable E]
  [DecidableEq E]
  {mu nu : ProbabilityMeasure (InfiniteCurrentConfig E)}
  {S : Finset E}
-- given
  (kernel : (↑S → Bool) → (↑S → ℕ) → ℝ≥0∞)
  (hparity : currentParityMarginalPMF mu S = currentParityMarginalPMF nu S)
  (hmu : ∀ a : ↑S → ℕ, (mu : Measure (InfiniteCurrentConfig E)) (currentCylinder S {a}) = (mu : Measure (InfiniteCurrentConfig E)) (currentParityPatternCylinder S (currentLocalParity a)) * kernel (currentLocalParity a) a)
  (hnu : ∀ a : ↑S → ℕ, (nu : Measure (InfiniteCurrentConfig E)) (currentCylinder S {a}) = (nu : Measure (InfiniteCurrentConfig E)) (currentParityPatternCylinder S (currentLocalParity a)) * kernel (currentLocalParity a) a) :
-- imply
  currentMarginal mu S = currentMarginal nu S := by
-- proof
  apply StatMech.FrontierB.currentMarginal_eq_of_parityMarginal_eq_of_pattern_factor mu nu S kernel hparity hmu hnu

/--
[ProbabilityMeasure.ext_of_currentParity_and_pattern_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSelectionIndependence.lean)
-/
@[path]
private lemma ext_of_currentParity_and_pattern_factor_eq
  [Countable E]
  [DecidableEq E]
  {mu nu : ProbabilityMeasure (InfiniteCurrentConfig E)}
-- given
  (kernel : ∀ S : Finset E, (↑S → Bool) → (↑S → ℕ) → ℝ≥0∞)
  (hparity : ∀ S, currentParityMarginalPMF mu S = currentParityMarginalPMF nu S)
  (hmu : ∀ (S : Finset E) (a : ↑S → ℕ), (mu : Measure (InfiniteCurrentConfig E)) (currentCylinder S {a}) = (mu : Measure (InfiniteCurrentConfig E)) (currentParityPatternCylinder S (currentLocalParity a)) * kernel S (currentLocalParity a) a)
  (hnu : ∀ (S : Finset E) (a : ↑S → ℕ), (nu : Measure (InfiniteCurrentConfig E)) (currentCylinder S {a}) = (nu : Measure (InfiniteCurrentConfig E)) (currentParityPatternCylinder S (currentLocalParity a)) * kernel S (currentLocalParity a) a) :
-- imply
  mu = nu := by
-- proof
  apply StatMech.FrontierB.ProbabilityMeasure.ext_of_currentParity_and_pattern_factor mu nu kernel hparity hmu hnu

/--
[WeakCurrentConverges.pattern_factor_of_eventually](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSelectionIndependence.lean)
-/
@[path]
private lemma pattern_factor_of_eventually_eq
  [Countable E]
  [DecidableEq E]
  {mu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E)}
  {nu : ProbabilityMeasure (InfiniteCurrentConfig E)}
  {S : Finset E}
  {a : ↑S → ℕ}
-- given
  (hnu : WeakCurrentConverges mu nu)
  (kernel : (↑S → Bool) → (↑S → ℕ) → ℝ≥0∞)
  (hkernelTop : ∀ odd a, kernel odd a ≠ ⊤)
  (hfactor : ∀ a : ↑S → ℕ, ∀ᶠ n in atTop, (mu n : Measure (InfiniteCurrentConfig E)) (currentCylinder S {a}) = (mu n : Measure (InfiniteCurrentConfig E)) (currentParityPatternCylinder S (currentLocalParity a)) * kernel (currentLocalParity a) a) :
-- imply
  (nu : Measure (InfiniteCurrentConfig E)) (currentCylinder S {a}) = (nu : Measure (InfiniteCurrentConfig E)) (currentParityPatternCylinder S (currentLocalParity a)) * kernel (currentLocalParity a) a := by
-- proof
  apply StatMech.FrontierB.WeakCurrentConverges.pattern_factor_of_eventually hnu S kernel hkernelTop hfactor a

/--
[currentLimit_eq_of_avoid_tendsto_of_pattern_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSelectionIndependence.lean)
-/
@[path]
private lemma currentLimit_eq_of_avoid_tendsto_of_pattern_factor_eq
  [Countable E]
  [DecidableEq E]
  {mu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E)}
  {nu rho : ProbabilityMeasure (InfiniteCurrentConfig E)}
  {phi psi : ℕ → ℕ}
-- given
  (havoid : ∀ A : Finset E, ∃ L : ℝ≥0∞, Tendsto (fun n => (mu n : Measure (InfiniteCurrentConfig E)) (currentParityAvoidCylinder A)) atTop (nhds L))
  (kernel : ∀ S : Finset E, (↑S → Bool) → (↑S → ℕ) → ℝ≥0∞)
  (hphi : StrictMono phi)
  (hpsi : StrictMono psi)
  (hnu : WeakCurrentConverges (mu ∘ phi) nu)
  (hrho : WeakCurrentConverges (mu ∘ psi) rho)
  (hnuFactor : ∀ (S : Finset E) (a : ↑S → ℕ), (nu : Measure (InfiniteCurrentConfig E)) (currentCylinder S {a}) = (nu : Measure (InfiniteCurrentConfig E)) (currentParityPatternCylinder S (currentLocalParity a)) * kernel S (currentLocalParity a) a)
  (hrhoFactor : ∀ (S : Finset E) (a : ↑S → ℕ), (rho : Measure (InfiniteCurrentConfig E)) (currentCylinder S {a}) = (rho : Measure (InfiniteCurrentConfig E)) (currentParityPatternCylinder S (currentLocalParity a)) * kernel S (currentLocalParity a) a) :
-- imply
  nu = rho := by
-- proof
  apply StatMech.FrontierB.currentLimit_eq_of_avoid_tendsto_of_pattern_factor mu havoid kernel hphi hpsi hnu hrho hnuFactor hrhoFactor

/--
[ambientSubfinset_lattice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSelectionIndependence.lean)
-/
@[path]
private lemma ambientSubfinset_lattice_eq
  {d : ℕ}
  {S : Finset (Sym2 (Site d))}
  {T : Finset ↑S}
-- given
  (hS : (↑S : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet) :
-- imply
  (↑(ambientSubfinset S T) : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet := by
-- proof
  apply StatMech.FrontierB.ambientSubfinset_lattice d S hS T

/--
[plusCurrentLimit_parityMarginal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSelectionIndependence.lean)
-/
@[path]
private lemma plusCurrentLimit_parityMarginal_eq_eq
  {d : ℕ}
  {beta : ℝ}
  {S : Finset (Sym2 (Site d))}
  {nu rho : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
  {phi psi : ℕ → ℕ}
-- given
  (hbeta : 0 ≤ beta)
  (hS : (↑S : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet)
  (hphi : StrictMono phi)
  (hpsi : StrictMono psi)
  (hnu : WeakCurrentConverges ((fun n => plusBoxCurrentMeasure d n beta hbeta) ∘ phi) nu)
  (hrho : WeakCurrentConverges ((fun n => plusBoxCurrentMeasure d n beta hbeta) ∘ psi) rho) :
-- imply
  currentParityMarginalPMF nu S = currentParityMarginalPMF rho S := by
-- proof
  apply StatMech.FrontierB.plusCurrentLimit_parityMarginal_eq d beta hbeta S hS hphi hpsi hnu hrho

/--
[freeCurrentLimit_parityMarginal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSelectionIndependence.lean)
-/
@[path]
private lemma freeCurrentLimit_parityMarginal_eq_eq
  {d : ℕ}
  {beta : ℝ}
  {S : Finset (Sym2 (Site d))}
  {nu rho : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
  {phi psi : ℕ → ℕ}
-- given
  (hbeta : 0 ≤ beta)
  (hS : (↑S : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet)
  (hphi : StrictMono phi)
  (hpsi : StrictMono psi)
  (hnu : WeakCurrentConverges ((fun n => freeBoxCurrentMeasure d n beta hbeta) ∘ phi) nu)
  (hrho : WeakCurrentConverges ((fun n => freeBoxCurrentMeasure d n beta hbeta) ∘ psi) rho) :
-- imply
  currentParityMarginalPMF nu S = currentParityMarginalPMF rho S := by
-- proof
  apply StatMech.FrontierB.freeCurrentLimit_parityMarginal_eq d beta hbeta S hS hphi hpsi hnu hrho

/--
[plusCurrentLimit_pattern_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSelectionIndependence.lean)
-/
@[path]
private lemma plusCurrentLimit_pattern_factor_eq
  {d : ℕ}
  {beta : ℝ}
  {S : Finset (Sym2 (Site d))}
  {nu : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
  {phi : ℕ → ℕ}
  {a : ↑S → ℕ}
-- given
  (hbeta : 0 < beta)
  (hS : (↑S : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet)
  (hphi : StrictMono phi)
  (hnu : WeakCurrentConverges ((fun n => plusBoxCurrentMeasure d n beta hbeta.le) ∘ phi) nu) :
-- imply
  (nu : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) (currentCylinder S {a}) = (nu : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) (currentParityPatternCylinder S (currentLocalParity a)) * finiteParityPMF S beta hbeta (currentLocalParity a) a := by
-- proof
  apply StatMech.FrontierB.plusCurrentLimit_pattern_factor d beta hbeta S hS hphi hnu a

/--
[freeCurrentLimit_pattern_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSelectionIndependence.lean)
-/
@[path]
private lemma freeCurrentLimit_pattern_factor_eq
  {d : ℕ}
  {beta : ℝ}
  {S : Finset (Sym2 (Site d))}
  {nu : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
  {phi : ℕ → ℕ}
  {a : ↑S → ℕ}
-- given
  (hbeta : 0 < beta)
  (hS : (↑S : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet)
  (hphi : StrictMono phi)
  (hnu : WeakCurrentConverges ((fun n => freeBoxCurrentMeasure d n beta hbeta.le) ∘ phi) nu) :
-- imply
  (nu : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) (currentCylinder S {a}) = (nu : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) (currentParityPatternCylinder S (currentLocalParity a)) * finiteParityPMF S beta hbeta (currentLocalParity a) a := by
-- proof
  apply StatMech.FrontierB.freeCurrentLimit_pattern_factor d beta hbeta S hS hphi hnu a

/--
[plusCurrentLimit_latticeMarginal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSelectionIndependence.lean)
-/
@[path]
private lemma plusCurrentLimit_latticeMarginal_eq_eq
  {d : ℕ}
  {beta : ℝ}
  {S : Finset (Sym2 (Site d))}
  {nu rho : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
  {phi psi : ℕ → ℕ}
-- given
  (hbeta : 0 < beta)
  (hS : (↑S : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet)
  (hphi : StrictMono phi)
  (hpsi : StrictMono psi)
  (hnu : WeakCurrentConverges ((fun n => plusBoxCurrentMeasure d n beta hbeta.le) ∘ phi) nu)
  (hrho : WeakCurrentConverges ((fun n => plusBoxCurrentMeasure d n beta hbeta.le) ∘ psi) rho) :
-- imply
  currentMarginal nu S = currentMarginal rho S := by
-- proof
  apply StatMech.FrontierB.plusCurrentLimit_latticeMarginal_eq d beta hbeta S hS hphi hpsi hnu hrho

/--
[freeCurrentLimit_latticeMarginal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSelectionIndependence.lean)
-/
@[path]
private lemma freeCurrentLimit_latticeMarginal_eq_eq
  {d : ℕ}
  {beta : ℝ}
  {S : Finset (Sym2 (Site d))}
  {nu rho : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
  {phi psi : ℕ → ℕ}
-- given
  (hbeta : 0 < beta)
  (hS : (↑S : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet)
  (hphi : StrictMono phi)
  (hpsi : StrictMono psi)
  (hnu : WeakCurrentConverges ((fun n => freeBoxCurrentMeasure d n beta hbeta.le) ∘ phi) nu)
  (hrho : WeakCurrentConverges ((fun n => freeBoxCurrentMeasure d n beta hbeta.le) ∘ psi) rho) :
-- imply
  currentMarginal nu S = currentMarginal rho S := by
-- proof
  apply StatMech.FrontierB.freeCurrentLimit_latticeMarginal_eq d beta hbeta S hS hphi hpsi hnu hrho

/--
[boxCurrentEdgeIncl_mem_lattice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSelectionIndependence.lean)
-/
@[path]
private lemma boxCurrentEdgeIncl_mem_lattice_eq
  {d n : ℕ}
  {e : (StatMech.FK.boxGraph d n).edgeFinset} :
-- imply
  boxCurrentEdgeIncl d n e ∈ (hypercubicLattice d).edgeSet := by
-- proof
  apply StatMech.FrontierB.boxCurrentEdgeIncl_mem_lattice d n e

/--
[boxCurrentEdgeIncl_ne_nonlattice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSelectionIndependence.lean)
-/
@[path]
private lemma boxCurrentEdgeIncl_ne_nonlattice_eq
  {d n : ℕ}
  {e : Sym2 (Site d)}
-- given
  (he : e ∉ (hypercubicLattice d).edgeSet) :
-- imply
  e ∉ Set.range (boxCurrentEdgeIncl d n) := by
-- proof
  apply StatMech.FrontierB.boxCurrentEdgeIncl_ne_nonlattice d n e he

/--
[freeBoxCurrentMeasure_nonlattice_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSelectionIndependence.lean)
-/
@[path]
private lemma freeBoxCurrentMeasure_nonlattice_zero_eq
  {d n : ℕ}
  {beta : ℝ}
  {e : Sym2 (Site d)}
-- given
  (hbeta : 0 ≤ beta)
  (he : e ∉ (hypercubicLattice d).edgeSet) :
-- imply
  (freeBoxCurrentMeasure d n beta hbeta : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) {m | m e = 0} = 1 := by
-- proof
  apply StatMech.FrontierB.freeBoxCurrentMeasure_nonlattice_zero d n beta hbeta e he

/--
[plusBoxCurrentMeasure_nonlattice_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSelectionIndependence.lean)
-/
@[path]
private lemma plusBoxCurrentMeasure_nonlattice_zero_eq
  {d n : ℕ}
  {beta : ℝ}
  {e : Sym2 (Site d)}
-- given
  (hbeta : 0 ≤ beta)
  (he : e ∉ (hypercubicLattice d).edgeSet) :
-- imply
  (plusBoxCurrentMeasure d n beta hbeta : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) {m | m e = 0} = 1 := by
-- proof
  apply StatMech.FrontierB.plusBoxCurrentMeasure_nonlattice_zero d n beta hbeta e he

/--
[plusCurrentLimit_nonlattice_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSelectionIndependence.lean)
-/
@[path]
private lemma plusCurrentLimit_nonlattice_zero_eq
  {d : ℕ}
  {beta : ℝ}
  {e : Sym2 (Site d)}
  {nu : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
  {phi : ℕ → ℕ}
-- given
  (hbeta : 0 ≤ beta)
  (he : e ∉ (hypercubicLattice d).edgeSet)
  (hnu : WeakCurrentConverges ((fun n => plusBoxCurrentMeasure d n beta hbeta) ∘ phi) nu) :
-- imply
  (nu : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) {m | m e = 0} = 1 := by
-- proof
  apply StatMech.FrontierB.plusCurrentLimit_nonlattice_zero d beta hbeta e he hnu

/--
[freeCurrentLimit_nonlattice_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSelectionIndependence.lean)
-/
@[path]
private lemma freeCurrentLimit_nonlattice_zero_eq
  {d : ℕ}
  {beta : ℝ}
  {e : Sym2 (Site d)}
  {nu : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
  {phi : ℕ → ℕ}
-- given
  (hbeta : 0 ≤ beta)
  (he : e ∉ (hypercubicLattice d).edgeSet)
  (hnu : WeakCurrentConverges ((fun n => freeBoxCurrentMeasure d n beta hbeta) ∘ phi) nu) :
-- imply
  (nu : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) {m | m e = 0} = 1 := by
-- proof
  apply StatMech.FrontierB.freeCurrentLimit_nonlattice_zero d beta hbeta e he hnu

/--
[latticeEdgePart_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSelectionIndependence.lean)
-/
@[path]
private lemma latticeEdgePart_subset_eq
  {d : ℕ}
  {S : Finset (Sym2 (Site d))} :
-- imply
  latticeEdgePart d S ⊆ S := by
-- proof
  apply StatMech.FrontierB.latticeEdgePart_subset d S

/--
[latticeEdgePart_lattice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSelectionIndependence.lean)
-/
@[path]
private lemma latticeEdgePart_lattice_eq
  {d : ℕ}
  {S : Finset (Sym2 (Site d))} :
-- imply
  (↑(latticeEdgePart d S) : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet := by
-- proof
  apply StatMech.FrontierB.latticeEdgePart_lattice d S

/--
[ae_eq_zero_of_measure_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSelectionIndependence.lean)
-/
@[path]
private lemma ae_eq_zero_of_measure_eq_one_eq
  [Countable E]
  {mu : ProbabilityMeasure (InfiniteCurrentConfig E)}
  {e : E}
-- given
  (hzero : (mu : Measure (InfiniteCurrentConfig E)) {m | m e = 0} = 1) :
-- imply
  ∀ᵐ m ∂(mu : Measure (InfiniteCurrentConfig E)), m e = 0 := by
-- proof
  apply StatMech.FrontierB.ae_eq_zero_of_measure_eq_one mu e hzero

/--
[ae_nonlattice_zero_on_finset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSelectionIndependence.lean)
-/
@[path]
private lemma ae_nonlattice_zero_on_finset_eq
  {d : ℕ}
  {mu : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
  {S : Finset (Sym2 (Site d))}
-- given
  (hzero : ∀ e, e ∉ (hypercubicLattice d).edgeSet → (mu : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) {m | m e = 0} = 1) :
-- imply
  ∀ᵐ m ∂(mu : Measure (InfiniteCurrentConfig (Sym2 (Site d)))), ∀ e ∈ S, e ∉ (hypercubicLattice d).edgeSet → m e = 0 := by
-- proof
  apply StatMech.FrontierB.ae_nonlattice_zero_on_finset d mu S hzero

/--
[currentCylinder_singleton_reduce_lattice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSelectionIndependence.lean)
-/
@[path]
private lemma currentCylinder_singleton_reduce_lattice_eq
  {d : ℕ}
  {mu : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
  {S : Finset (Sym2 (Site d))}
  {a : ↑S → ℕ}
-- given
  (hzero : ∀ e, e ∉ (hypercubicLattice d).edgeSet → (mu : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) {m | m e = 0} = 1) :
-- imply
  (mu : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) (currentCylinder S {a}) = if ∀ e : ↑S, e.1 ∉ (hypercubicLattice d).edgeSet → a e = 0 then (mu : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) (currentCylinder (latticeEdgePart d S) {Finset.restrict₂ (π := fun _ : Sym2 (Site d) => ℕ) (latticeEdgePart_subset d S) a}) else 0 := by
-- proof
  apply StatMech.FrontierB.currentCylinder_singleton_reduce_lattice d mu S hzero a

/--
[plusCurrentLimit_marginal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSelectionIndependence.lean)
-/
@[path]
private lemma plusCurrentLimit_marginal_eq_eq
  {d : ℕ}
  {beta : ℝ}
  {S : Finset (Sym2 (Site d))}
  {nu rho : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
  {phi psi : ℕ → ℕ}
-- given
  (hbeta : 0 < beta)
  (hphi : StrictMono phi)
  (hpsi : StrictMono psi)
  (hnu : WeakCurrentConverges ((fun n => plusBoxCurrentMeasure d n beta hbeta.le) ∘ phi) nu)
  (hrho : WeakCurrentConverges ((fun n => plusBoxCurrentMeasure d n beta hbeta.le) ∘ psi) rho) :
-- imply
  currentMarginal nu S = currentMarginal rho S := by
-- proof
  apply StatMech.FrontierB.plusCurrentLimit_marginal_eq d beta hbeta S hphi hpsi hnu hrho

/--
[freeCurrentLimit_marginal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSelectionIndependence.lean)
-/
@[path]
private lemma freeCurrentLimit_marginal_eq_eq
  {d : ℕ}
  {beta : ℝ}
  {S : Finset (Sym2 (Site d))}
  {nu rho : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
  {phi psi : ℕ → ℕ}
-- given
  (hbeta : 0 < beta)
  (hphi : StrictMono phi)
  (hpsi : StrictMono psi)
  (hnu : WeakCurrentConverges ((fun n => freeBoxCurrentMeasure d n beta hbeta.le) ∘ phi) nu)
  (hrho : WeakCurrentConverges ((fun n => freeBoxCurrentMeasure d n beta hbeta.le) ∘ psi) rho) :
-- imply
  currentMarginal nu S = currentMarginal rho S := by
-- proof
  apply StatMech.FrontierB.freeCurrentLimit_marginal_eq d beta hbeta S hphi hpsi hnu hrho

/--
[plusCurrentLimit_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSelectionIndependence.lean)
-/
@[path]
private lemma plusCurrentLimit_eq_eq
  {d : ℕ}
  {beta : ℝ}
  {nu rho : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
  {phi psi : ℕ → ℕ}
-- given
  (hbeta : 0 < beta)
  (hphi : StrictMono phi)
  (hpsi : StrictMono psi)
  (hnu : WeakCurrentConverges ((fun n => plusBoxCurrentMeasure d n beta hbeta.le) ∘ phi) nu)
  (hrho : WeakCurrentConverges ((fun n => plusBoxCurrentMeasure d n beta hbeta.le) ∘ psi) rho) :
-- imply
  nu = rho := by
-- proof
  apply StatMech.FrontierB.plusCurrentLimit_eq d beta hbeta hphi hpsi hnu hrho

/--
[freeCurrentLimit_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSelectionIndependence.lean)
-/
@[path]
private lemma freeCurrentLimit_eq_eq
  {d : ℕ}
  {beta : ℝ}
  {nu rho : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
  {phi psi : ℕ → ℕ}
-- given
  (hbeta : 0 < beta)
  (hphi : StrictMono phi)
  (hpsi : StrictMono psi)
  (hnu : WeakCurrentConverges ((fun n => freeBoxCurrentMeasure d n beta hbeta.le) ∘ phi) nu)
  (hrho : WeakCurrentConverges ((fun n => freeBoxCurrentMeasure d n beta hbeta.le) ∘ psi) rho) :
-- imply
  nu = rho := by
-- proof
  apply StatMech.FrontierB.freeCurrentLimit_eq d beta hbeta hphi hpsi hnu hrho

/--
[plusCurrentLimit_eq_infinitePlus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSelectionIndependence.lean)
-/
@[path]
private lemma plusCurrentLimit_eq_infinitePlus_eq
  {d : ℕ}
  {beta : ℝ}
  {nu : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
  {phi : ℕ → ℕ}
-- given
  (hbeta : 0 < beta)
  (hphi : StrictMono phi)
  (hnu : WeakCurrentConverges ((fun n => plusBoxCurrentMeasure d n beta hbeta.le) ∘ phi) nu) :
-- imply
  nu = infinitePlusCurrentMeasure d beta hbeta.le := by
-- proof
  apply StatMech.FrontierB.plusCurrentLimit_eq_infinitePlus d beta hbeta hphi hnu

/--
[freeCurrentLimit_eq_infiniteFree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSelectionIndependence.lean)
-/
@[path]
private lemma freeCurrentLimit_eq_infiniteFree_eq
  {d : ℕ}
  {beta : ℝ}
  {nu : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
  {phi : ℕ → ℕ}
-- given
  (hbeta : 0 < beta)
  (hphi : StrictMono phi)
  (hnu : WeakCurrentConverges ((fun n => freeBoxCurrentMeasure d n beta hbeta.le) ∘ phi) nu) :
-- imply
  nu = infiniteFreeCurrentMeasure d beta hbeta.le := by
-- proof
  apply StatMech.FrontierB.freeCurrentLimit_eq_infiniteFree d beta hbeta hphi hnu

/--
[weakCurrent_tendsto_of_tight_of_subseq_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSelectionIndependence.lean)
-/
@[path]
private lemma weakCurrent_tendsto_of_tight_of_subseq_unique_eq
  [Countable E]
  {mu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E)}
  {nu : ProbabilityMeasure (InfiniteCurrentConfig E)}
-- given
  (htight : IsTightMeasureSet (Set.range fun n => (mu n : Measure (InfiniteCurrentConfig E))))
  (hnuMem : nu ∈ closure (Set.range mu))
  (hunique : ∀ (rho : ProbabilityMeasure (InfiniteCurrentConfig E)) (phi : ℕ → ℕ), StrictMono phi → WeakCurrentConverges (mu ∘ phi) rho → rho = nu) :
-- imply
  WeakCurrentConverges mu nu := by
-- proof
  apply StatMech.FrontierB.weakCurrent_tendsto_of_tight_of_subseq_unique mu nu htight hnuMem hunique

/--
[plusBoxCurrentMeasure_tendsto_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSelectionIndependence.lean)
-/
@[path]
private lemma plusBoxCurrentMeasure_tendsto_full_eq
  {d : ℕ}
  {beta : ℝ}
-- given
  (hbeta : 0 < beta) :
-- imply
  WeakCurrentConverges (fun n => plusBoxCurrentMeasure d n beta hbeta.le) (infinitePlusCurrentMeasure d beta hbeta.le) := by
-- proof
  apply StatMech.FrontierB.plusBoxCurrentMeasure_tendsto_full d beta hbeta

/--
[freeBoxCurrentMeasure_tendsto_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSelectionIndependence.lean)
-/
@[path]
private lemma freeBoxCurrentMeasure_tendsto_full_eq
  {d : ℕ}
  {beta : ℝ}
-- given
  (hbeta : 0 < beta) :
-- imply
  WeakCurrentConverges (fun n => freeBoxCurrentMeasure d n beta hbeta.le) (infiniteFreeCurrentMeasure d beta hbeta.le) := by
-- proof
  apply StatMech.FrontierB.freeBoxCurrentMeasure_tendsto_full d beta hbeta

/--
[plusBoxCurrentMeasure_cylinder_tendsto_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSelectionIndependence.lean)
-/
@[path]
private lemma plusBoxCurrentMeasure_cylinder_tendsto_full_eq
  {d : ℕ}
  {beta : ℝ}
  {S : Finset (Sym2 (Site d))}
  {A : Set (↑S → ℕ)}
-- given
  (hbeta : 0 < beta) :
-- imply
  Tendsto (fun n => (plusBoxCurrentMeasure d n beta hbeta.le : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) (currentCylinder S A)) atTop (nhds ((infinitePlusCurrentMeasure d beta hbeta.le : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) (currentCylinder S A))) := by
-- proof
  apply StatMech.FrontierB.plusBoxCurrentMeasure_cylinder_tendsto_full d beta hbeta S A

/--
[freeBoxCurrentMeasure_cylinder_tendsto_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSelectionIndependence.lean)
-/
@[path]
private lemma freeBoxCurrentMeasure_cylinder_tendsto_full_eq
  {d : ℕ}
  {beta : ℝ}
  {S : Finset (Sym2 (Site d))}
  {A : Set (↑S → ℕ)}
-- given
  (hbeta : 0 < beta) :
-- imply
  Tendsto (fun n => (freeBoxCurrentMeasure d n beta hbeta.le : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) (currentCylinder S A)) atTop (nhds ((infiniteFreeCurrentMeasure d beta hbeta.le : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) (currentCylinder S A))) := by
-- proof
  apply StatMech.FrontierB.freeBoxCurrentMeasure_cylinder_tendsto_full d beta hbeta S A


-- created on 2026-10-23
