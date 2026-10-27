import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Percolation.Theta
open MeasureTheory StatMech StatMech.Percolation


/--
[mem_percolationEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Theta.lean)
-/
@[path]
private lemma mem_percolationEvent_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  ω ∈ percolationEvent d ↔ (StatMech.Lattice.cluster d ω (origin d)).Infinite := by
-- proof
  apply StatMech.Percolation.mem_percolationEvent

/--
[mem_subcriticalSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Theta.lean)
-/
@[path]
private lemma mem_subcriticalSet_eq
  {d : ℕ}
  {p : ℝ≥0} :
-- imply
  p ∈ subcriticalSet d ↔ ∃ hp : p ≤ 1, theta d p hp = 0 := by
-- proof
  apply StatMech.Percolation.mem_subcriticalSet

/--
[theta_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Theta.lean)
-/
@[path]
private lemma theta_nonneg_eq
  {d : ℕ}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  0 ≤ theta d p hp := by
-- proof
  apply StatMech.Percolation.theta_nonneg d p hp

/--
[theta_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Theta.lean)
-/
@[path]
private lemma theta_le_one_eq
  {d : ℕ}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  theta d p hp ≤ 1 := by
-- proof
  apply StatMech.Percolation.theta_le_one d p hp


-- created on 2026-10-23
