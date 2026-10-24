import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierB.CurrentLimitTranslation
open MeasureTheory Filter Topology StatMech StatMech.FrontierB


/--
[currentShiftFinsetEquiv_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentLimitTranslation.lean)
-/
@[path]
private lemma currentShiftFinsetEquiv_val_eq
  [Group H]
  [MulAction H E]
  [DecidableEq E]
  {g : H}
  {S : Finset E}
  {e : ↑(currentShiftFinset g S)} :
-- imply
  (currentShiftFinsetEquiv g S e).1 = g • e.1 := by
-- proof
  apply StatMech.FrontierB.currentShiftFinsetEquiv_val g S e

/--
[currentShiftFinsetEquiv_symm_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentLimitTranslation.lean)
-/
@[path]
private lemma currentShiftFinsetEquiv_symm_val_eq
  [Group H]
  [MulAction H E]
  [DecidableEq E]
  {g : H}
  {S : Finset E}
  {e : ↑S} :
-- imply
  ((currentShiftFinsetEquiv g S).symm e).1 = g⁻¹ • e.1 := by
-- proof
  apply StatMech.FrontierB.currentShiftFinsetEquiv_symm_val g S e

/--
[currentLocalParity_shiftPattern](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentLimitTranslation.lean)
-/
@[path]
private lemma currentLocalParity_shiftPattern_eq
  [Group H]
  [MulAction H E]
  [DecidableEq E]
  {g : H}
  {S : Finset E}
-- given
  (a : ↑S -> Nat) :
-- imply
  currentLocalParity (currentShiftPattern g S a) = currentShiftPattern g S (currentLocalParity a) := by
-- proof
  apply StatMech.FrontierB.currentLocalParity_shiftPattern g S a

/--
[preimage_currentCylinder_singleton_currentShift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentLimitTranslation.lean)
-/
@[path]
private lemma preimage_currentCylinder_singleton_currentShift_eq
  [Group H]
  [MulAction H E]
  [DecidableEq E]
  {g : H}
  {S : Finset E}
-- given
  (a : ↑S -> Nat) :
-- imply
  (currentShift g) ⁻¹' currentCylinder S {a} = currentCylinder (currentShiftFinset g S) {currentShiftPattern g S a} := by
-- proof
  apply StatMech.FrontierB.preimage_currentCylinder_singleton_currentShift g S a

/--
[currentShiftFinset_lattice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentLimitTranslation.lean)
-/
@[path]
private lemma currentShiftFinset_lattice_eq
  {d : Nat}
  {g : Multiplicative (Site d)}
  {S : Finset (Sym2 (Site d))}
-- given
  (hS : (↑S : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet) :
-- imply
  (↑(currentShiftFinset g S) : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet := by
-- proof
  apply StatMech.FrontierB.currentShiftFinset_lattice d g S hS

/--
[preimage_currentParityAvoidCylinder_currentShift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentLimitTranslation.lean)
-/
@[path]
private lemma preimage_currentParityAvoidCylinder_currentShift_eq
  [Group H]
  [MulAction H E]
  [DecidableEq E]
  {g : H}
  {F : Finset E} :
-- imply
  (currentShift g) ⁻¹' currentParityAvoidCylinder F = currentParityAvoidCylinder (currentShiftFinset g F) := by
-- proof
  apply StatMech.FrontierB.preimage_currentParityAvoidCylinder_currentShift g F

/--
[edgeSpinSum_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentLimitTranslation.lean)
-/
@[path]
private lemma edgeSpinSum_shift_eq
  {d : Nat}
  {g : Multiplicative (Site d)}
  {F : Finset (Sym2 (Site d))}
  {omega : ConfigSpace (Site d)} :
-- imply
  edgeSpinSum F (ConfigSpace.shift g omega) = edgeSpinSum (currentShiftFinset g F) omega := by
-- proof
  apply StatMech.FrontierB.edgeSpinSum_shift d g F omega

/--
[integral_exp_neg_edgeSpinSum_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentLimitTranslation.lean)
-/
@[path]
private lemma integral_exp_neg_edgeSpinSum_shift_eq
  {d : Nat}
  {beta : Real}
  {mu : Measure (ConfigSpace (Site d))}
  {g : Multiplicative (Site d)}
  {F : Finset (Sym2 (Site d))}
-- given
  (hti : ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d)) mu) :
-- imply
  (∫ omega, Real.exp (-beta * edgeSpinSum (currentShiftFinset g F) omega) ∂mu) = ∫ omega, Real.exp (-beta * edgeSpinSum F omega) ∂mu := by
-- proof
  apply StatMech.FrontierB.integral_exp_neg_edgeSpinSum_shift d beta mu hti g F

/--
[infinitePlusCurrentMeasure_parityAvoid_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentLimitTranslation.lean)
-/
@[path]
private lemma infinitePlusCurrentMeasure_parityAvoid_eq_eq
  {d : Nat}
  {beta : Real}
  {F : Finset (Sym2 (Site d))}
-- given
  (hbeta : 0 < beta)
  (hF : (↑F : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet) :
-- imply
  (infinitePlusCurrentMeasure d beta hbeta.le : Measure _) (currentParityAvoidCylinder F) = ENNReal.ofReal ((∫ omega, Real.exp (-beta * edgeSpinSum F omega) ∂(plusState d beta 0 : Measure (ConfigSpace (Site d)))) * Real.cosh beta ^ F.card) := by
-- proof
  apply StatMech.FrontierB.infinitePlusCurrentMeasure_parityAvoid_eq d beta hbeta F hF

/--
[infiniteFreeCurrentMeasure_parityAvoid_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentLimitTranslation.lean)
-/
@[path]
private lemma infiniteFreeCurrentMeasure_parityAvoid_eq_eq
  {d : Nat}
  {beta : Real}
  {F : Finset (Sym2 (Site d))}
-- given
  (hbeta : 0 < beta)
  (hF : (↑F : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet) :
-- imply
  (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _) (currentParityAvoidCylinder F) = ENNReal.ofReal ((∫ omega, Real.exp (-beta * edgeSpinSum F omega) ∂(freeState d beta 0 : Measure (ConfigSpace (Site d)))) * Real.cosh beta ^ F.card) := by
-- proof
  apply StatMech.FrontierB.infiniteFreeCurrentMeasure_parityAvoid_eq d beta hbeta F hF

/--
[finiteParityPMF_shiftPattern](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentLimitTranslation.lean)
-/
@[path]
private lemma finiteParityPMF_shiftPattern_eq
  [Group H]
  [MulAction H E]
  [DecidableEq E]
  {g : H}
  {S : Finset E}
  {beta : Real}
-- given
  (hbeta : 0 < beta)
  (odd : ↑S -> Bool)
  (a : ↑S -> Nat) :
-- imply
  finiteParityPMF (currentShiftFinset g S) beta hbeta (currentShiftPattern g S odd) (currentShiftPattern g S a) = finiteParityPMF S beta hbeta odd a := by
-- proof
  apply StatMech.FrontierB.finiteParityPMF_shiftPattern g S beta hbeta odd a

/--
[preimage_currentParityPatternCylinder_currentShift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentLimitTranslation.lean)
-/
@[path]
private lemma preimage_currentParityPatternCylinder_currentShift_eq
  [Group H]
  [MulAction H E]
  [DecidableEq E]
  {g : H}
  {S : Finset E}
-- given
  (odd : ↑S -> Bool) :
-- imply
  (currentShift g) ⁻¹' currentParityPatternCylinder S odd = currentParityPatternCylinder (currentShiftFinset g S) (currentShiftPattern g S odd) := by
-- proof
  apply StatMech.FrontierB.preimage_currentParityPatternCylinder_currentShift g S odd

/--
[currentShiftLaw_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentLimitTranslation.lean)
-/
@[path]
private lemma currentShiftLaw_apply_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {g : H}
  {mu : ProbabilityMeasure (InfiniteCurrentConfig E)}
  {A : Set (InfiniteCurrentConfig E)}
-- given
  (hA : MeasurableSet A) :
-- imply
  (currentShiftLaw g mu : Measure (InfiniteCurrentConfig E)) A = (mu : Measure (InfiniteCurrentConfig E)) ((currentShift g) ⁻¹' A) := by
-- proof
  apply StatMech.FrontierB.currentShiftLaw_apply g mu A hA

/--
[currentParityMarginalPMF_currentShiftLaw_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentLimitTranslation.lean)
-/
@[path]
private lemma currentParityMarginalPMF_currentShiftLaw_eq_eq
  {d : Nat}
  {mu : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
  {g : Multiplicative (Site d)}
  {S : Finset (Sym2 (Site d))}
-- given
  (havoid : ∀ F : Finset (Sym2 (Site d)), (↑F : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet -> (mu : Measure _) ((currentShift g) ⁻¹' currentParityAvoidCylinder F) = (mu : Measure _) (currentParityAvoidCylinder F))
  (hS : (↑S : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet) :
-- imply
  currentParityMarginalPMF (currentShiftLaw g mu) S = currentParityMarginalPMF mu S := by
-- proof
  apply StatMech.FrontierB.currentParityMarginalPMF_currentShiftLaw_eq d mu g havoid S hS

/--
[currentLimit_isTranslationInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentLimitTranslation.lean)
-/
@[path]
private lemma currentLimit_isTranslationInvariant_eq
  {d : Nat}
  {beta : Real}
  {mu : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
-- given
  (hbeta : 0 < beta)
  (hzero : ∀ e, e ∉ (hypercubicLattice d).edgeSet -> (mu : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) {m : InfiniteCurrentConfig (Sym2 (Site d)) | m e = 0} = 1)
  (hfactor : ∀ (S : Finset (Sym2 (Site d))), (↑S : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet -> ∀ a : ↑S -> Nat, (mu : Measure _) (currentCylinder S {a}) = (mu : Measure _) (currentParityPatternCylinder S (currentLocalParity a)) * finiteParityPMF S beta hbeta (currentLocalParity a) a)
  (havoid : ∀ (g : Multiplicative (Site d)) (F : Finset (Sym2 (Site d))), (↑F : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet -> (mu : Measure _) ((currentShift g) ⁻¹' currentParityAvoidCylinder F) = (mu : Measure _) (currentParityAvoidCylinder F)) :
-- imply
  CurrentIsTranslationInvariant (H := Multiplicative (Site d)) (mu : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FrontierB.currentLimit_isTranslationInvariant d beta hbeta mu hzero hfactor havoid

/--
[infinitePlusCurrentMeasure_isTranslationInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentLimitTranslation.lean)
-/
@[path]
private lemma infinitePlusCurrentMeasure_isTranslationInvariant_eq
  {d : Nat}
  {beta : Real}
-- given
  (hbeta : 0 < beta) :
-- imply
  CurrentIsTranslationInvariant (H := Multiplicative (Site d)) (infinitePlusCurrentMeasure d beta hbeta.le : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FrontierB.infinitePlusCurrentMeasure_isTranslationInvariant d beta hbeta

/--
[infiniteFreeCurrentMeasure_isTranslationInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentLimitTranslation.lean)
-/
@[path]
private lemma infiniteFreeCurrentMeasure_isTranslationInvariant_eq
  {d : Nat}
  {beta : Real}
-- given
  (hbeta : 0 < beta) :
-- imply
  CurrentIsTranslationInvariant (H := Multiplicative (Site d)) (infiniteFreeCurrentMeasure d beta hbeta.le : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FrontierB.infiniteFreeCurrentMeasure_isTranslationInvariant d beta hbeta


-- created on 2026-10-23
