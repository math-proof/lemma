import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bfcfaithful
open Set SimpleGraph Finset StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech.Walls


/--
[bff_allOpen_box_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfcfaithful.lean)
-/
@[path]
private lemma bff_allOpen_box_connected_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℕ}
  {x y : Site 2}
-- given
  (h : bff_BoxAllOpen ω n)
  (hx : x ∈ Lattice.box 2 n)
  (hy : y ∈ Lattice.box 2 n) :
-- imply
  Lattice.Connected 2 ω x y := by
-- proof
  apply StatMech.Walls.bff_allOpen_box_connected h hx hy

/--
[bff_upperLines_box_edge_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfcfaithful.lean)
-/
@[path]
private lemma bff_upperLines_box_edge_mem_eq
  {L : ℕ}
-- given
  (hL : 1 ≤ L) :
-- imply
  s(bc57_pt 0 0, bc57_pt 1 0) ∈ boxEdges 2 L := by
-- proof
  apply StatMech.Walls.bff_upperLines_box_edge_mem hL

/--
[bff_upperLines_box_edge_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfcfaithful.lean)
-/
@[path]
private lemma bff_upperLines_box_edge_closed_eq :
-- imply
  bc60_upperLines s(bc57_pt 0 0, bc57_pt 1 0) = false := by
-- proof
  apply StatMech.Walls.bff_upperLines_box_edge_closed

/--
[bff_upperLines_box_not_allOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfcfaithful.lean)
-/
@[path]
private lemma bff_upperLines_box_not_allOpen_eq
  {L : ℕ}
-- given
  (hL : 1 ≤ L) :
-- imply
  ¬ bff_BoxAllOpen bc60_upperLines L := by
-- proof
  apply StatMech.Walls.bff_upperLines_box_not_allOpen hL

/--
[bff_genuine_trif_with_non_allOpen_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfcfaithful.lean)
-/
@[path]
private lemma bff_genuine_trif_with_non_allOpen_box_eq
  {L : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  bc67_IsGnTrifurcation bc60_upperLines L (0 : Site 2) ∧ ¬ bff_BoxAllOpen bc60_upperLines L := by
-- proof
  apply StatMech.Walls.bff_genuine_trif_with_non_allOpen_box hL


-- created on 2026-10-23
