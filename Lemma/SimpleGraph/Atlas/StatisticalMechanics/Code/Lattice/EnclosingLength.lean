import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.EnclosingLength.Part2
open Finset Set SimpleGraph StatMech StatMech.Lattice


/--
[closedWalk_length_ge_two_l1dist](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EnclosingLength.lean)
-/
@[path]
private lemma closedWalk_length_ge_two_l1dist_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {G : SimpleGraph (Site 2)}
  {u : Site 2}
  {c : G.Walk u u}
  {b : Site 2}
-- given
  (hle : G ≤ hypercubicLattice 2)
  (hb : b ∈ c.support) :
-- imply
  2 * l1dist 2 u b ≤ c.length := by
-- proof
  apply StatMech.Lattice.closedWalk_length_ge_two_l1dist hle c hb

/--
[enclExitFaceUp_coord0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EnclosingLength.lean)
-/
@[path]
private lemma enclExitFaceUp_coord0_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  (exitFaceUp (ω := ω) hfin) 0 = (exitIndex (ω := ω) hfin : ℤ) := by
-- proof
  apply StatMech.Lattice.enclExitFaceUp_coord0 hfin

/--
[exitIndex_le_l1dist_of_leftFace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EnclosingLength.lean)
-/
@[path]
private lemma exitIndex_le_l1dist_of_leftFace_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {w : Site 2}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hw : w 0 ≤ 0) :
-- imply
  (exitIndex (ω := ω) hfin : ℕ) ≤ l1dist 2 (exitFaceUp (ω := ω) hfin) w := by
-- proof
  apply StatMech.Lattice.exitIndex_le_l1dist_of_leftFace hfin hw

/--
[anchoredCycleExists_of_leftFace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EnclosingLength.lean)
-/
@[path]
private lemma anchoredCycleExists_of_leftFace_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hlf : CycleHasLeftFace ω hfin) :
-- imply
  AnchoredCycleExists ω hfin := by
-- proof
  apply StatMech.Lattice.anchoredCycleExists_of_leftFace hfin hlf

/--
[anchoredEnclosure_of_cycleHasLeftFace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EnclosingLength.lean)
-/
@[path]
private lemma anchoredEnclosure_of_cycleHasLeftFace_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hlf : CycleHasLeftFace ω hfin) :
-- imply
  ∃ (u : Site 2) (c : (faceBoundaryGraph (cluster 2 ω (origin 2))).Walk u u), c.IsCycle ∧ u ∈ anchorFinset c.length := by
-- proof
  apply StatMech.Lattice.anchoredEnclosure_of_cycleHasLeftFace hfin hlf

/--
[pcAnchoredEnclosure_of_cycleHasLeftFace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EnclosingLength.lean)
-/
@[path]
private lemma pcAnchoredEnclosure_of_cycleHasLeftFace_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hlf : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite), CycleHasLeftFace ω hfin) :
-- imply
  StatMech.Percolation.PcAnchoredEnclosure := by
-- proof
  apply StatMech.Lattice.pcAnchoredEnclosure_of_cycleHasLeftFace hlf


-- created on 2026-10-23
