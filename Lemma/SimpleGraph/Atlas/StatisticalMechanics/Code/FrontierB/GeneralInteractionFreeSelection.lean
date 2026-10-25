import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.GeneralInteractionFreeSelection.Part2
open Filter MeasureTheory Set Topology StatMech StatMech.FrontierB


/--
[interactionBoxEdgeIncl_liftIndex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeSelection.lean)
-/
@[path]
private lemma interactionBoxEdgeIncl_liftIndex_eq
  {d n : Nat}
  {F : Finset (Sym2 (Site d))}
  {e : ↑F}
-- given
  (hFbox : ∀ e ∈ F, ∀ x ∈ e, x ∈ box d n)
  (hFdiag : ∀ e ∈ F, ¬e.IsDiag) :
-- imply
  interactionBoxEdgeIncl d n (interactionBoxLiftIndexEmbedding F hFbox hFdiag e) = e.1 := by
-- proof
  apply StatMech.FrontierB.interactionBoxEdgeIncl_liftIndex F hFbox hFdiag e

/--
[restrictCurrent_extendInteractionBoxCurrent_lift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeSelection.lean)
-/
@[path]
private lemma restrictCurrent_extendInteractionBoxCurrent_lift_eq
  {d n : Nat}
  {F : Finset (Sym2 (Site d))}
  {m : EdgeCurrent (interactionBoxGraph d n)}
-- given
  (hFbox : ∀ e ∈ F, ∀ x ∈ e, x ∈ box d n)
  (hFdiag : ∀ e ∈ F, ¬e.IsDiag) :
-- imply
  restrictCurrent F (extendInteractionBoxCurrent d n m) = fun e => restrictCurrent (interactionBoxLiftedEdgeIndices F hFbox hFdiag) m (interactionBoxLiftIndexEquiv F hFbox hFdiag e) := by
-- proof
  apply StatMech.FrontierB.restrictCurrent_extendInteractionBoxCurrent_lift F hFbox hFdiag m

/--
[nonnegativeFiniteParityKernel_pullback](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeSelection.lean)
-/
@[path]
private lemma nonnegativeFiniteParityKernel_pullback_eq
  {d n : Nat}
  {J : Sym2 (Site d) → ℝ}
  {beta : ℝ}
  {F : Finset (Sym2 (Site d))}
  {a : ↑F → Nat}
-- given
  (hFbox : ∀ e ∈ F, ∀ x ∈ e, x ∈ box d n)
  (hFdiag : ∀ e ∈ F, ¬e.IsDiag) :
-- imply
  nonnegativeFiniteParityKernel (interactionBoxLiftedEdgeIndices F hFbox hFdiag) (fun e : (interactionBoxGraph d n).edgeFinset => beta * interactionBoxCoupling J n e.1) (currentLocalParity (interactionBoxPullbackPattern F hFbox hFdiag a)) (interactionBoxPullbackPattern F hFbox hFdiag a) = nonnegativeFiniteParityKernel F (fun e => beta * J e) (currentLocalParity a) a := by
-- proof
  apply StatMech.FrontierB.nonnegativeFiniteParityKernel_pullback J beta F hFbox hFdiag a

/--
[preimage_currentCylinder_singleton_extendInteractionBoxCurrent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeSelection.lean)
-/
@[path]
private lemma preimage_currentCylinder_singleton_extendInteractionBoxCurrent_eq
  {d n : Nat}
  {F : Finset (Sym2 (Site d))}
  {a : ↑F → Nat}
-- given
  (hFbox : ∀ e ∈ F, ∀ x ∈ e, x ∈ box d n)
  (hFdiag : ∀ e ∈ F, ¬e.IsDiag) :
-- imply
  extendInteractionBoxCurrent d n ⁻¹' currentCylinder F {a} = {m | restrictCurrent (interactionBoxLiftedEdgeIndices F hFbox hFdiag) m = interactionBoxPullbackPattern F hFbox hFdiag a} := by
-- proof
  apply StatMech.FrontierB.preimage_currentCylinder_singleton_extendInteractionBoxCurrent F hFbox hFdiag a

/--
[preimage_currentParityPatternCylinder_extendInteractionBoxCurrent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeSelection.lean)
-/
@[path]
private lemma preimage_currentParityPatternCylinder_extendInteractionBoxCurrent_eq
  {d n : Nat}
  {F : Finset (Sym2 (Site d))}
  {odd : ↑F → Bool}
-- given
  (hFbox : ∀ e ∈ F, ∀ x ∈ e, x ∈ box d n)
  (hFdiag : ∀ e ∈ F, ¬e.IsDiag) :
-- imply
  extendInteractionBoxCurrent d n ⁻¹' currentParityPatternCylinder F odd = {m | currentLocalParity (restrictCurrent (interactionBoxLiftedEdgeIndices F hFbox hFdiag) m) = odd ∘ (interactionBoxLiftIndexEquiv F hFbox hFdiag).symm} := by
-- proof
  apply StatMech.FrontierB.preimage_currentParityPatternCylinder_extendInteractionBoxCurrent F hFbox hFdiag odd

/--
[sourcelessNonnegativeCurrentLocalParityPMF](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeSelection.lean)
-/
@[path]
private lemma sourcelessNonnegativeCurrentLocalParityPMF_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset G.edgeFinset}
-- given
  (hbeta : 0 < beta)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  PMF.map currentLocalParity (PMF.map (restrictCurrent S) (sourcelessCurrentPMF G beta J hbeta.le hJ)) = PMF.map (restrictParity G S) (sourcelessNonnegativeParityPMF G beta J hbeta.le hJ) := by
-- proof
  apply StatMech.FrontierB.sourcelessNonnegativeCurrentLocalParityPMF G beta hbeta J hJ S

/--
[generalFreeBoxCurrentMeasure_pattern_factor_nonDiagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeSelection.lean)
-/
@[path]
private lemma generalFreeBoxCurrentMeasure_pattern_factor_nonDiagonal_eq
  {d n : Nat}
  {J : Sym2 (Site d) → ℝ}
  {beta : ℝ}
  {F : Finset (Sym2 (Site d))}
  {a : ↑F → Nat}
-- given
  (hJ : ∀ e, 0 ≤ J e)
  (hbeta : 0 < beta)
  (hFbox : ∀ e ∈ F, ∀ x ∈ e, x ∈ box d n)
  (hFdiag : ∀ e ∈ F, ¬e.IsDiag) :
-- imply
  (generalFreeBoxCurrentMeasure J hJ n beta hbeta.le : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) (currentCylinder F {a}) = (generalFreeBoxCurrentMeasure J hJ n beta hbeta.le : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) (currentParityPatternCylinder F (currentLocalParity a)) * nonnegativeFiniteParityPMF F (fun e ↦ beta * J e) (fun e : ↑F ↦ mul_nonneg hbeta.le (hJ e.1)) (currentLocalParity a) a := by
-- proof
  apply StatMech.FrontierB.generalFreeBoxCurrentMeasure_pattern_factor_nonDiagonal J hJ beta hbeta F hFbox hFdiag a

/--
[generalFreeCurrentLimit_pattern_factor_nonDiagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeSelection.lean)
-/
@[path]
private lemma generalFreeCurrentLimit_pattern_factor_nonDiagonal_eq
  {d : Nat}
  {J : Sym2 (Site d) → ℝ}
  {beta : ℝ}
  {S : Finset (Sym2 (Site d))}
  {nu : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
  {phi : Nat → Nat}
  {a : ↑S → Nat}
-- given
  (hJ : ∀ e, 0 ≤ J e)
  (hbeta : 0 < beta)
  (hSdiag : ∀ e ∈ S, ¬e.IsDiag)
  (hphi : StrictMono phi)
  (hnu : WeakCurrentConverges ((fun n ↦ generalFreeBoxCurrentMeasure J hJ n beta hbeta.le) ∘ phi) nu) :
-- imply
  (nu : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) (currentCylinder S {a}) = (nu : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) (currentParityPatternCylinder S (currentLocalParity a)) * nonnegativeFiniteParityPMF S (fun e ↦ beta * J e) (fun e : ↑S ↦ mul_nonneg hbeta.le (hJ e.1)) (currentLocalParity a) a := by
-- proof
  apply StatMech.FrontierB.generalFreeCurrentLimit_pattern_factor_nonDiagonal J hJ beta hbeta S hSdiag hphi hnu a

/--
[generalFreeCurrentLimit_parityMarginal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeSelection.lean)
-/
@[path]
private lemma generalFreeCurrentLimit_parityMarginal_eq_eq
  {d : Nat}
  {J : Sym2 (Site d) → ℝ}
  {beta : ℝ}
  {S : Finset (Sym2 (Site d))}
  {nu rho : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
  {phi psi : Nat → Nat}
-- given
  (hJ : ∀ e, 0 ≤ J e)
  (hbeta : 0 < beta)
  (hphi : StrictMono phi)
  (hpsi : StrictMono psi)
  (hnu : WeakCurrentConverges ((fun n => generalFreeBoxCurrentMeasure J hJ n beta hbeta.le) ∘ phi) nu)
  (hrho : WeakCurrentConverges ((fun n => generalFreeBoxCurrentMeasure J hJ n beta hbeta.le) ∘ psi) rho) :
-- imply
  currentParityMarginalPMF nu S = currentParityMarginalPMF rho S := by
-- proof
  apply StatMech.FrontierB.generalFreeCurrentLimit_parityMarginal_eq J hJ beta hbeta S hphi hpsi hnu hrho

/--
[generalFreeCurrentLimit_nonDiagonalMarginal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeSelection.lean)
-/
@[path]
private lemma generalFreeCurrentLimit_nonDiagonalMarginal_eq_eq
  {d : Nat}
  {J : Sym2 (Site d) → ℝ}
  {beta : ℝ}
  {S : Finset (Sym2 (Site d))}
  {nu rho : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
  {phi psi : Nat → Nat}
-- given
  (hJ : ∀ e, 0 ≤ J e)
  (hbeta : 0 < beta)
  (hSdiag : ∀ e ∈ S, ¬e.IsDiag)
  (hphi : StrictMono phi)
  (hpsi : StrictMono psi)
  (hnu : WeakCurrentConverges ((fun n ↦ generalFreeBoxCurrentMeasure J hJ n beta hbeta.le) ∘ phi) nu)
  (hrho : WeakCurrentConverges ((fun n ↦ generalFreeBoxCurrentMeasure J hJ n beta hbeta.le) ∘ psi) rho) :
-- imply
  currentMarginal nu S = currentMarginal rho S := by
-- proof
  apply StatMech.FrontierB.generalFreeCurrentLimit_nonDiagonalMarginal_eq J hJ beta hbeta S hSdiag hphi hpsi hnu hrho

/--
[generalFreeBoxCurrentMeasure_diag_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeSelection.lean)
-/
@[path]
private lemma generalFreeBoxCurrentMeasure_diag_zero_eq
  {d : Nat}
  {J : Sym2 (Site d) → ℝ}
  {n : Nat}
  {beta : ℝ}
  {e : Sym2 (Site d)}
-- given
  (hJ : ∀ e, 0 ≤ J e)
  (hbeta : 0 ≤ beta)
  (he : e.IsDiag) :
-- imply
  (generalFreeBoxCurrentMeasure J hJ n beta hbeta : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) {m | m e = 0} = 1 := by
-- proof
  apply StatMech.FrontierB.generalFreeBoxCurrentMeasure_diag_zero J hJ n beta hbeta e he

/--
[generalFreeCurrentLimit_diag_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeSelection.lean)
-/
@[path]
private lemma generalFreeCurrentLimit_diag_zero_eq
  {d : Nat}
  {J : Sym2 (Site d) → ℝ}
  {beta : ℝ}
  {e : Sym2 (Site d)}
  {nu : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
  {phi : Nat → Nat}
-- given
  (hJ : ∀ e, 0 ≤ J e)
  (hbeta : 0 ≤ beta)
  (he : e.IsDiag)
  (hnu : WeakCurrentConverges ((fun n ↦ generalFreeBoxCurrentMeasure J hJ n beta hbeta) ∘ phi) nu) :
-- imply
  (nu : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) {m | m e = 0} = 1 := by
-- proof
  apply StatMech.FrontierB.generalFreeCurrentLimit_diag_zero J hJ beta hbeta e he hnu

/--
[nonDiagonalEdgeFinset_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeSelection.lean)
-/
@[path]
private lemma nonDiagonalEdgeFinset_subset_eq
  [DecidableEq V]
  {S : Finset (Sym2 V)} :
-- imply
  nonDiagonalEdgeFinset S ⊆ S := by
-- proof
  apply StatMech.FrontierB.nonDiagonalEdgeFinset_subset S

/--
[nonDiagonalEdgeFinset_nonDiag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeSelection.lean)
-/
@[path]
private lemma nonDiagonalEdgeFinset_nonDiag_eq
  [DecidableEq V]
  {S : Finset (Sym2 V)} :
-- imply
  ∀ e ∈ nonDiagonalEdgeFinset S, ¬e.IsDiag := by
-- proof
  apply StatMech.FrontierB.nonDiagonalEdgeFinset_nonDiag S

/--
[ae_diagonal_zero_on_finset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeSelection.lean)
-/
@[path]
private lemma ae_diagonal_zero_on_finset_eq
  {d : Nat}
  {mu : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
  {S : Finset (Sym2 (Site d))}
-- given
  (hzero : ∀ e, e.IsDiag → (mu : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) {m | m e = 0} = 1) :
-- imply
  ∀ᵐ m ∂(mu : Measure (InfiniteCurrentConfig (Sym2 (Site d)))), ∀ e ∈ S, e.IsDiag → m e = 0 := by
-- proof
  apply StatMech.FrontierB.ae_diagonal_zero_on_finset mu S hzero

/--
[currentCylinder_singleton_reduce_nonDiagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeSelection.lean)
-/
@[path]
private lemma currentCylinder_singleton_reduce_nonDiagonal_eq
  {d : Nat}
  {mu : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
  {S : Finset (Sym2 (Site d))}
  {a : ↑S → Nat}
-- given
  (hzero : ∀ e, e.IsDiag → (mu : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) {m | m e = 0} = 1) :
-- imply
  (mu : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) (currentCylinder S {a}) = if ∀ e : ↑S, e.1.IsDiag → a e = 0 then (mu : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) (currentCylinder (nonDiagonalEdgeFinset S) {Finset.restrict₂ (π := fun _ : Sym2 (Site d) ↦ Nat) (nonDiagonalEdgeFinset_subset S) a}) else 0 := by
-- proof
  apply StatMech.FrontierB.currentCylinder_singleton_reduce_nonDiagonal mu S hzero a

/--
[generalFreeCurrentLimit_marginal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeSelection.lean)
-/
@[path]
private lemma generalFreeCurrentLimit_marginal_eq_eq
  {d : Nat}
  {J : Sym2 (Site d) → ℝ}
  {beta : ℝ}
  {S : Finset (Sym2 (Site d))}
  {nu rho : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
  {phi psi : Nat → Nat}
-- given
  (hJ : ∀ e, 0 ≤ J e)
  (hbeta : 0 < beta)
  (hphi : StrictMono phi)
  (hpsi : StrictMono psi)
  (hnu : WeakCurrentConverges ((fun n ↦ generalFreeBoxCurrentMeasure J hJ n beta hbeta.le) ∘ phi) nu)
  (hrho : WeakCurrentConverges ((fun n ↦ generalFreeBoxCurrentMeasure J hJ n beta hbeta.le) ∘ psi) rho) :
-- imply
  currentMarginal nu S = currentMarginal rho S := by
-- proof
  apply StatMech.FrontierB.generalFreeCurrentLimit_marginal_eq J hJ beta hbeta S hphi hpsi hnu hrho

/--
[generalFreeCurrentLimit_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeSelection.lean)
-/
@[path]
private lemma generalFreeCurrentLimit_eq_eq
  {d : Nat}
  {J : Sym2 (Site d) → ℝ}
  {beta : ℝ}
  {nu rho : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
  {phi psi : Nat → Nat}
-- given
  (hJ : ∀ e, 0 ≤ J e)
  (hbeta : 0 < beta)
  (hphi : StrictMono phi)
  (hpsi : StrictMono psi)
  (hnu : WeakCurrentConverges ((fun n ↦ generalFreeBoxCurrentMeasure J hJ n beta hbeta.le) ∘ phi) nu)
  (hrho : WeakCurrentConverges ((fun n ↦ generalFreeBoxCurrentMeasure J hJ n beta hbeta.le) ∘ psi) rho) :
-- imply
  nu = rho := by
-- proof
  apply StatMech.FrontierB.generalFreeCurrentLimit_eq J hJ beta hbeta hphi hpsi hnu hrho

/--
[generalFreeCurrentLimit_eq_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeSelection.lean)
-/
@[path]
private lemma generalFreeCurrentLimit_eq_infinite_eq
  {d : Nat}
  {I : SummableFerromagneticInteraction d}
  {beta : ℝ}
  {nu : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
  {phi : Nat → Nat}
-- given
  (hbeta : 0 < beta)
  (hphi : StrictMono phi)
  (hnu : WeakCurrentConverges ((fun n ↦ generalFreeBoxCurrentMeasure I.coupling I.nonneg n beta hbeta.le) ∘ phi) nu) :
-- imply
  nu = generalInfiniteFreeCurrentMeasure I beta hbeta.le := by
-- proof
  apply StatMech.FrontierB.generalFreeCurrentLimit_eq_infinite I beta hbeta hphi hnu

/--
[generalFreeBoxCurrentMeasure_tendsto_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeSelection.lean)
-/
@[path]
private lemma generalFreeBoxCurrentMeasure_tendsto_full_eq
  {d : Nat}
  {I : SummableFerromagneticInteraction d}
  {beta : ℝ}
-- given
  (hbeta : 0 < beta) :
-- imply
  WeakCurrentConverges (fun n ↦ generalFreeBoxCurrentMeasure I.coupling I.nonneg n beta hbeta.le) (generalInfiniteFreeCurrentMeasure I beta hbeta.le) := by
-- proof
  apply StatMech.FrontierB.generalFreeBoxCurrentMeasure_tendsto_full I beta hbeta

/--
[generalFreeBoxCurrentMeasure_cylinder_tendsto_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeSelection.lean)
-/
@[path]
private lemma generalFreeBoxCurrentMeasure_cylinder_tendsto_full_eq
  {d : Nat}
  {I : SummableFerromagneticInteraction d}
  {beta : ℝ}
  {S : Finset (Sym2 (Site d))}
  {A : Set (↑S → Nat)}
-- given
  (hbeta : 0 < beta) :
-- imply
  Tendsto (fun n ↦ (generalFreeBoxCurrentMeasure I.coupling I.nonneg n beta hbeta.le : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) (currentCylinder S A)) atTop (nhds ((generalInfiniteFreeCurrentMeasure I beta hbeta.le : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) (currentCylinder S A))) := by
-- proof
  apply StatMech.FrontierB.generalFreeBoxCurrentMeasure_cylinder_tendsto_full I beta hbeta S A


-- created on 2026-10-23
