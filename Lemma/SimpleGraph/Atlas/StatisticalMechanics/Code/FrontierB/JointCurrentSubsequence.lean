import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.JointCurrentSubsequence
open Filter MeasureTheory StatMech StatMech.FrontierB


/--
[freePlusBoxCurrentMeasure_joint_subsequence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/JointCurrentSubsequence.lean)
-/
@[path]
private lemma freePlusBoxCurrentMeasure_joint_subsequence_eq
  {d : ℕ}
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  ∃ (nuFree nuPlus : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))) (phi : ℕ → ℕ), StrictMono phi ∧ WeakCurrentConverges ((fun n => freeBoxCurrentMeasure d n beta hbeta) ∘ phi) nuFree ∧ WeakCurrentConverges ((fun n => plusBoxCurrentMeasure d n beta hbeta) ∘ phi) nuPlus := by
-- proof
  apply StatMech.FrontierB.freePlusBoxCurrentMeasure_joint_subsequence d beta hbeta

/--
[freePlusBoxCurrentMeasure_joint_subsequence_with_cylinders](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/JointCurrentSubsequence.lean)
-/
@[path]
private lemma freePlusBoxCurrentMeasure_joint_subsequence_with_cylinders_eq
  {d : ℕ}
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  ∃ (nuFree nuPlus : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))) (phi : ℕ → ℕ), StrictMono phi ∧ WeakCurrentConverges ((fun n => freeBoxCurrentMeasure d n beta hbeta) ∘ phi) nuFree ∧ WeakCurrentConverges ((fun n => plusBoxCurrentMeasure d n beta hbeta) ∘ phi) nuPlus ∧ ∀ (S : Finset (Sym2 (Site d))) (A : Set (↑S → ℕ)), Tendsto (fun k => freeBoxCurrentMeasure d (phi k) beta hbeta (currentCylinder S A)) atTop (nhds (nuFree (currentCylinder S A))) ∧ Tendsto (fun k => plusBoxCurrentMeasure d (phi k) beta hbeta (currentCylinder S A)) atTop (nhds (nuPlus (currentCylinder S A))) := by
-- proof
  apply StatMech.FrontierB.freePlusBoxCurrentMeasure_joint_subsequence_with_cylinders d beta hbeta


-- created on 2026-10-23
