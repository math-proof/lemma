import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.GeneralInteractionPlusSelection.Part2
open Filter MeasureTheory Set Topology StatMech StatMech.FrontierB


/--
[generalPlusCurrentLimit_pattern_factor_nonDiagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionPlusSelection.lean)
-/
@[path]
private lemma generalPlusCurrentLimit_pattern_factor_nonDiagonal_eq
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
  (hnu : WeakCurrentConverges ((fun n ↦ generalPlusBoxCurrentMeasure J hJ n beta hbeta.le) ∘ phi) nu) :
-- imply
  (nu : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) (currentCylinder S {a}) = (nu : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) (currentParityPatternCylinder S (currentLocalParity a)) * nonnegativeFiniteParityPMF S (fun e ↦ beta * J e) (fun e : ↑S ↦ mul_nonneg hbeta.le (hJ e.1)) (currentLocalParity a) a := by
-- proof
  apply StatMech.FrontierB.generalPlusCurrentLimit_pattern_factor_nonDiagonal J hJ beta hbeta S hSdiag hphi hnu a

/--
[generalPlusCurrentLimit_parityMarginal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionPlusSelection.lean)
-/
@[path]
private lemma generalPlusCurrentLimit_parityMarginal_eq_eq
  {d : Nat}
  {J : Sym2 (Site d) → ℝ}
  {beta : ℝ}
  {S : Finset (Sym2 (Site d))}
  {nu rho : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
  {phi psi : Nat → Nat}
-- given
  (hJ : ∀ e, 0 ≤ J e)
  (hbeta : 0 < beta)
  (havoid : GeneralPlusParityAvoidanceConverges J hJ beta hbeta)
  (hphi : StrictMono phi)
  (hpsi : StrictMono psi)
  (hnu : WeakCurrentConverges ((fun n ↦ generalPlusBoxCurrentMeasure J hJ n beta hbeta.le) ∘ phi) nu)
  (hrho : WeakCurrentConverges ((fun n ↦ generalPlusBoxCurrentMeasure J hJ n beta hbeta.le) ∘ psi) rho) :
-- imply
  currentParityMarginalPMF nu S = currentParityMarginalPMF rho S := by
-- proof
  apply StatMech.FrontierB.generalPlusCurrentLimit_parityMarginal_eq J hJ beta hbeta havoid S hphi hpsi hnu hrho

/--
[generalPlusCurrentLimit_nonDiagonalMarginal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionPlusSelection.lean)
-/
@[path]
private lemma generalPlusCurrentLimit_nonDiagonalMarginal_eq_eq
  {d : Nat}
  {J : Sym2 (Site d) → ℝ}
  {beta : ℝ}
  {S : Finset (Sym2 (Site d))}
  {nu rho : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
  {phi psi : Nat → Nat}
-- given
  (hJ : ∀ e, 0 ≤ J e)
  (hbeta : 0 < beta)
  (havoid : GeneralPlusParityAvoidanceConverges J hJ beta hbeta)
  (hSdiag : ∀ e ∈ S, ¬e.IsDiag)
  (hphi : StrictMono phi)
  (hpsi : StrictMono psi)
  (hnu : WeakCurrentConverges ((fun n ↦ generalPlusBoxCurrentMeasure J hJ n beta hbeta.le) ∘ phi) nu)
  (hrho : WeakCurrentConverges ((fun n ↦ generalPlusBoxCurrentMeasure J hJ n beta hbeta.le) ∘ psi) rho) :
-- imply
  currentMarginal nu S = currentMarginal rho S := by
-- proof
  apply StatMech.FrontierB.generalPlusCurrentLimit_nonDiagonalMarginal_eq J hJ beta hbeta havoid S hSdiag hphi hpsi hnu hrho

/--
[generalPlusBoxCurrentMeasure_diag_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionPlusSelection.lean)
-/
@[path]
private lemma generalPlusBoxCurrentMeasure_diag_zero_eq
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
  (generalPlusBoxCurrentMeasure J hJ n beta hbeta : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) {m | m e = 0} = 1 := by
-- proof
  apply StatMech.FrontierB.generalPlusBoxCurrentMeasure_diag_zero J hJ n beta hbeta e he

/--
[generalPlusCurrentLimit_diag_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionPlusSelection.lean)
-/
@[path]
private lemma generalPlusCurrentLimit_diag_zero_eq
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
  (hnu : WeakCurrentConverges ((fun n ↦ generalPlusBoxCurrentMeasure J hJ n beta hbeta) ∘ phi) nu) :
-- imply
  (nu : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) {m | m e = 0} = 1 := by
-- proof
  apply StatMech.FrontierB.generalPlusCurrentLimit_diag_zero J hJ beta hbeta e he hnu

/--
[generalPlusCurrentLimit_marginal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionPlusSelection.lean)
-/
@[path]
private lemma generalPlusCurrentLimit_marginal_eq_eq
  {d : Nat}
  {J : Sym2 (Site d) → ℝ}
  {beta : ℝ}
  {S : Finset (Sym2 (Site d))}
  {nu rho : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
  {phi psi : Nat → Nat}
-- given
  (hJ : ∀ e, 0 ≤ J e)
  (hbeta : 0 < beta)
  (havoid : GeneralPlusParityAvoidanceConverges J hJ beta hbeta)
  (hphi : StrictMono phi)
  (hpsi : StrictMono psi)
  (hnu : WeakCurrentConverges ((fun n ↦ generalPlusBoxCurrentMeasure J hJ n beta hbeta.le) ∘ phi) nu)
  (hrho : WeakCurrentConverges ((fun n ↦ generalPlusBoxCurrentMeasure J hJ n beta hbeta.le) ∘ psi) rho) :
-- imply
  currentMarginal nu S = currentMarginal rho S := by
-- proof
  apply StatMech.FrontierB.generalPlusCurrentLimit_marginal_eq J hJ beta hbeta havoid S hphi hpsi hnu hrho

/--
[generalPlusCurrentLimit_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionPlusSelection.lean)
-/
@[path]
private lemma generalPlusCurrentLimit_eq_eq
  {d : Nat}
  {J : Sym2 (Site d) → ℝ}
  {beta : ℝ}
  {nu rho : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
  {phi psi : Nat → Nat}
-- given
  (hJ : ∀ e, 0 ≤ J e)
  (hbeta : 0 < beta)
  (havoid : GeneralPlusParityAvoidanceConverges J hJ beta hbeta)
  (hphi : StrictMono phi)
  (hpsi : StrictMono psi)
  (hnu : WeakCurrentConverges ((fun n ↦ generalPlusBoxCurrentMeasure J hJ n beta hbeta.le) ∘ phi) nu)
  (hrho : WeakCurrentConverges ((fun n ↦ generalPlusBoxCurrentMeasure J hJ n beta hbeta.le) ∘ psi) rho) :
-- imply
  nu = rho := by
-- proof
  apply StatMech.FrontierB.generalPlusCurrentLimit_eq J hJ beta hbeta havoid hphi hpsi hnu hrho

/--
[generalPlusCurrentLimit_eq_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionPlusSelection.lean)
-/
@[path]
private lemma generalPlusCurrentLimit_eq_infinite_eq
  {d : Nat}
  {I : SummableFerromagneticInteraction d}
  {beta : ℝ}
  {nu : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
  {phi : Nat → Nat}
-- given
  (hbeta : 0 < beta)
  (havoid : GeneralPlusParityAvoidanceConverges I.coupling I.nonneg beta hbeta)
  (hphi : StrictMono phi)
  (hnu : WeakCurrentConverges ((fun n ↦ generalPlusBoxCurrentMeasure I.coupling I.nonneg n beta hbeta.le) ∘ phi) nu) :
-- imply
  nu = generalInfinitePlusCurrentMeasure I beta hbeta.le := by
-- proof
  apply StatMech.FrontierB.generalPlusCurrentLimit_eq_infinite I beta hbeta havoid hphi hnu

/--
[generalPlusBoxCurrentMeasure_tendsto_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionPlusSelection.lean)
-/
@[path]
private lemma generalPlusBoxCurrentMeasure_tendsto_full_eq
  {d : Nat}
  {I : SummableFerromagneticInteraction d}
  {beta : ℝ}
-- given
  (hbeta : 0 < beta)
  (havoid : GeneralPlusParityAvoidanceConverges I.coupling I.nonneg beta hbeta) :
-- imply
  WeakCurrentConverges (fun n ↦ generalPlusBoxCurrentMeasure I.coupling I.nonneg n beta hbeta.le) (generalInfinitePlusCurrentMeasure I beta hbeta.le) := by
-- proof
  apply StatMech.FrontierB.generalPlusBoxCurrentMeasure_tendsto_full I beta hbeta havoid

/--
[generalPlusBoxCurrentMeasure_cylinder_tendsto_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionPlusSelection.lean)
-/
@[path]
private lemma generalPlusBoxCurrentMeasure_cylinder_tendsto_full_eq
  {d : Nat}
  {I : SummableFerromagneticInteraction d}
  {beta : ℝ}
  {S : Finset (Sym2 (Site d))}
  {A : Set (↑S → Nat)}
-- given
  (hbeta : 0 < beta)
  (havoid : GeneralPlusParityAvoidanceConverges I.coupling I.nonneg beta hbeta) :
-- imply
  Tendsto (fun n ↦ (generalPlusBoxCurrentMeasure I.coupling I.nonneg n beta hbeta.le : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) (currentCylinder S A)) atTop (nhds ((generalInfinitePlusCurrentMeasure I beta hbeta.le : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) (currentCylinder S A))) := by
-- proof
  apply StatMech.FrontierB.generalPlusBoxCurrentMeasure_cylinder_tendsto_full I beta hbeta havoid S A


-- created on 2026-10-23
