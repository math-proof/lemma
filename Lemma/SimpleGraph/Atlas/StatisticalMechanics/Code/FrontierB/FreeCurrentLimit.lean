import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.FreeCurrentLimit
open Filter MeasureTheory StatMech StatMech.FrontierB


/--
[freeBoxCurrentMeasure_edge_inverse_tail_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeCurrentLimit.lean)
-/
@[path]
private lemma freeBoxCurrentMeasure_edge_inverse_tail_le_eq
  {d n : ℕ}
  {beta : ℝ}
  {e : Sym2 (Site d)}
  {K : ℕ}
-- given
  (hbeta : 0 ≤ beta)
  (hK : 0 < K) :
-- imply
  (freeBoxCurrentMeasure d n beta hbeta : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) {m | K ≤ m e} ≤ ENNReal.ofReal (Real.exp beta) / K := by
-- proof
  apply StatMech.FrontierB.freeBoxCurrentMeasure_edge_inverse_tail_le d n beta hbeta e K hK

/--
[freeBoxCurrentMeasure_tight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeCurrentLimit.lean)
-/
@[path]
private lemma freeBoxCurrentMeasure_tight_eq
  {d : ℕ}
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  IsTightMeasureSet (Set.range fun n => (freeBoxCurrentMeasure d n beta hbeta : Measure (InfiniteCurrentConfig (Sym2 (Site d))))) := by
-- proof
  apply StatMech.FrontierB.freeBoxCurrentMeasure_tight d beta hbeta

/--
[freeBoxCurrentMeasure_subsequence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeCurrentLimit.lean)
-/
@[path]
private lemma freeBoxCurrentMeasure_subsequence_eq
  {d : ℕ}
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  ∃ (nu : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))) (phi : ℕ → ℕ), StrictMono phi ∧ WeakCurrentConverges ((fun n => freeBoxCurrentMeasure d n beta hbeta) ∘ phi) nu := by
-- proof
  apply StatMech.FrontierB.freeBoxCurrentMeasure_subsequence d beta hbeta

/--
[freeBoxCurrentMeasure_subsequence_with_cylinders](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeCurrentLimit.lean)
-/
@[path]
private lemma freeBoxCurrentMeasure_subsequence_with_cylinders_eq
  {d : ℕ}
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  ∃ (nu : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))) (phi : ℕ → ℕ), StrictMono phi ∧ WeakCurrentConverges ((fun n => freeBoxCurrentMeasure d n beta hbeta) ∘ phi) nu ∧ ∀ (S : Finset (Sym2 (Site d))) (A : Set (↑S → ℕ)), Tendsto (fun k => freeBoxCurrentMeasure d (phi k) beta hbeta (currentCylinder S A)) atTop (nhds (nu (currentCylinder S A))) := by
-- proof
  apply StatMech.FrontierB.freeBoxCurrentMeasure_subsequence_with_cylinders d beta hbeta


-- created on 2026-10-23
