import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bindindep
open Set SimpleGraph Finset MeasureTheory StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech.Walls


/--
[bind_corridor_mem_I](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bindindep.lean)
-/
@[path]
private lemma bind_corridor_mem_I_eq :
-- imply
  s(bmf_a₁, bmf_b₁) ∈ bmf_I := by
-- proof
  apply StatMech.Walls.bind_corridor_mem_I

/--
[bind_removeSite_corridor_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bindindep.lean)
-/
@[path]
private lemma bind_removeSite_corridor_eq_eq
  {ω : ConfigSpace (Sym2 (Site 2))} :
-- imply
  removeSite 0 ω s(bmf_a₁, bmf_b₁) = ω s(bmf_a₁, bmf_b₁) := by
-- proof
  apply StatMech.Walls.bind_removeSite_corridor_eq ω

/--
[bind_corridor_openEdge_iff_I](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bindindep.lean)
-/
@[path]
private lemma bind_corridor_openEdge_iff_I_eq
  {ω : ConfigSpace (Sym2 (Site 2))} :
-- imply
  IsOpenEdge 2 (removeSite 0 ω) bmf_a₁ bmf_b₁ ↔ ω s(bmf_a₁, bmf_b₁) = true := by
-- proof
  apply StatMech.Walls.bind_corridor_openEdge_iff_I ω

/--
[bind_b](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bindindep.lean)
-/
@[path]
private lemma bind_b_eq :
-- imply
  bmf_b₁ ∈ s(bmf_a₁, bmf_b₁) := by
-- proof
  apply StatMech.Walls.bind_b

/--
[bind_a](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bindindep.lean)
-/
@[path]
private lemma bind_a_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : ω s(bmf_a₁, bmf_b₁) = true) :
-- imply
  bmf_a₁ ∈ cluster 2 (removeSite 0 ω) bmf_b₁ := by
-- proof
  apply StatMech.Walls.bind_a ω h


-- created on 2026-10-23
