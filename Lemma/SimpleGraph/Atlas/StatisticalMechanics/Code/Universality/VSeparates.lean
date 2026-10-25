import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.VSeparates.Part2
open Set SimpleGraph StatMech StatMech.Universality


/--
[liftWalk_support_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/VSeparates.lean)
-/
@[path]
private lemma liftWalk_support_mem_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : Set (Site 2)}
  {x y : R}
  {w : (openSubgraphInduce 2 ω R).Walk x y}
  {z : Site 2}
-- given
  (hz : z ∈ (liftWalk ω R w).support) :
-- imply
  ∃ (z' : R), z' ∈ w.support ∧ (z' : Site 2) = z := by
-- proof
  apply StatMech.Universality.liftWalk_support_mem ω R w hz

/--
[mem_colLeq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/VSeparates.lean)
-/
@[path]
private lemma mem_colLeq_eq
  {k : ℤ}
  {z : Site 2} :
-- imply
  z ∈ colLeq k ↔ z 0 ≤ k := by
-- proof
  apply StatMech.Universality.mem_colLeq k z

/--
[exists_bdEdge_colLeq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/VSeparates.lean)
-/
@[path]
private lemma exists_bdEdge_colLeq_eq
  {k α β : ℤ}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (hx : x 0 = α)
  (hy : y 0 = β)
  (hk1 : α ≤ k)
  (hk2 : k < β) :
-- imply
  ∃ e ∈ w.edges, bdEdge (colLeq k) e := by
-- proof
  apply StatMech.Universality.exists_bdEdge_colLeq hx hy hk1 hk2 w

/--
[hwalk_meets_column](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/VSeparates.lean)
-/
@[path]
private lemma hwalk_meets_column_eq
  {k α β : ℤ}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (hx : x 0 = α)
  (hy : y 0 = β)
  (hk1 : α ≤ k)
  (hk2 : k < β) :
-- imply
  ∃ z ∈ w.support, z 0 = k := by
-- proof
  apply StatMech.Universality.hwalk_meets_column hx hy hk1 hk2 w

/--
[boxCrossing_meets_column](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/VSeparates.lean)
-/
@[path]
private lemma boxCrossing_meets_column_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {α β c d k : ℤ}
  {x y : rect α β c d}
  {w : (openSubgraphInduce 2 ω (rect α β c d)).Walk x y}
-- given
  (hk1 : α ≤ k)
  (hk2 : k < β)
  (hx0 : (x : Site 2) 0 = α)
  (hy0 : (y : Site 2) 0 = β) :
-- imply
  ∃ z ∈ w.support, (z : Site 2) 0 = k := by
-- proof
  apply StatMech.Universality.boxCrossing_meets_column ω hk1 hk2 hx0 hy0 w


-- created on 2026-10-23
