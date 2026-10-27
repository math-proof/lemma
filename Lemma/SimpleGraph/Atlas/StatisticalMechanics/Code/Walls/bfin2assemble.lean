import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bfin2assemble
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bfin2_neighbor_in_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfin2assemble.lean)
-/
@[path]
private lemma bfin2_neighbor_in_box_eq
  {d : ℕ}
  {d R : ℕ}
  {x n : Site d}
-- given
  (hR : 1 ≤ R)
  (hx : x ∈ box d (R - 1))
  (hadj : (hypercubicLattice d).Adj x n) :
-- imply
  n ∈ box d R := by
-- proof
  apply StatMech.Walls.bfin2_neighbor_in_box hR hx hadj

/--
[bfin2_trifSet_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfin2assemble.lean)
-/
@[path]
private lemma bfin2_trifSet_finite_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {R : ℕ} :
-- imply
  {x : Site d | bft_FineTrif ω x ∧ x ∈ box d (R - 1)}.Finite := by
-- proof
  apply StatMech.Walls.bfin2_trifSet_finite ω R

/--
[bfin2_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfin2assemble.lean)
-/
@[path]
private lemma bfin2_count_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {R : ℕ}
-- given
  (hR : 1 ≤ R) :
-- imply
  (bfin2_trifSet_finite ω R).toFinset.card ≤ (vertexBoundary_finite d R).toFinset.card := by
-- proof
  apply StatMech.Walls.bfin2_count ω R hR


-- created on 2026-10-23
