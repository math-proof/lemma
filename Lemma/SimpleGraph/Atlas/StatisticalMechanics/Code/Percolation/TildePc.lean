import Mathlib
import sympy.Basic
import Def.StatisticalMechanics.Code.Percolation.TildePc.Part4
open MeasureTheory Finset StatMech StatMech.Percolation


/--
[connWithinProb_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TildePc.lean)
-/
@[path]
private lemma connWithinProb_nonneg_eq
  {d : ℕ}
  {d : ℕ}
  {S : Finset (Site d)}
  {x : Site d}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  0 ≤ connWithinProb d p hp S x := by
-- proof
  apply StatMech.Percolation.connWithinProb_nonneg d p hp S x

/--
[phi_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TildePc.lean)
-/
@[path]
private lemma phi_nonneg_eq
  {d : ℕ}
  {d : ℕ}
  {S : Finset (Site d)}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  0 ≤ phi d p hp S := by
-- proof
  apply StatMech.Percolation.phi_nonneg d p hp S

/--
[mem_tildePcSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TildePc.lean)
-/
@[path]
private lemma mem_tildePcSet_eq
  {d : ℕ}
  {d : ℕ}
  {p : ℝ≥0} :
-- imply
  p ∈ tildePcSet d ↔ ∃ hp : p ≤ 1, ∃ S : Finset (Site d), origin d ∈ S ∧ phi d p hp S < 1 := by
-- proof
  apply StatMech.Percolation.mem_tildePcSet


-- created on 2026-10-23
