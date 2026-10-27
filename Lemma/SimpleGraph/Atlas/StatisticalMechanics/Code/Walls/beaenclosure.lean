import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.beaenclosure.Part2
open Set SimpleGraph Finset StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bea_ce_true_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/beaenclosure.lean)
-/
@[path]
private lemma bea_ce_true_iff_eq
  {e : Sym2 (Site 2)} :
-- imply
  bea_ce e = true ↔ ((∃ k : ℤ, e = s(bc57_pt k 0, bc57_pt (k + 1) 0)) ∨ (∃ k : ℤ, e = s(bc57_pt k 1, bc57_pt (k + 1) 1)) ∨ (∃ k : ℤ, e = s(bc57_pt k (-1), bc57_pt (k + 1) (-1))) ∨ (e = s(bc57_pt 0 0, bc57_pt 0 1)) ∨ (e = s(bc57_pt 0 0, bc57_pt 0 (-1)))) := by
-- proof
  apply StatMech.Walls.bea_ce_true_iff e

/--
[bea_line_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/beaenclosure.lean)
-/
@[path]
private lemma bea_line_open_eq
  {h : ℤ}
  {k : ℤ}
-- given
  (hh : h = 0 ∨ h = 1 ∨ h = -1) :
-- imply
  bea_ce s(bc57_pt k h, bc57_pt (k + 1) h) = true := by
-- proof
  apply StatMech.Walls.bea_line_open hh k

/--
[bea_bridgeUp_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/beaenclosure.lean)
-/
@[path]
private lemma bea_bridgeUp_open_eq :
-- imply
  bea_ce s(bc57_pt 0 0, bc57_pt 0 1) = true := by
-- proof
  apply StatMech.Walls.bea_bridgeUp_open

/--
[bea_bridgeDown_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/beaenclosure.lean)
-/
@[path]
private lemma bea_bridgeDown_open_eq :
-- imply
  bea_ce s(bc57_pt 0 0, bc57_pt 0 (-1)) = true := by
-- proof
  apply StatMech.Walls.bea_bridgeDown_open

/--
[bea_vert_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/beaenclosure.lean)
-/
@[path]
private lemma bea_vert_adj_eq
-- given
  (h : ℤ) :
-- imply
  (hypercubicLattice 2).Adj (bc57_pt 0 h) (bc57_pt 0 (h + 1)) := by
-- proof
  apply StatMech.Walls.bea_vert_adj h

/--
[bea_out_O](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/beaenclosure.lean)
-/
@[path]
private lemma bea_out_O_eq
  {c h : ℤ}
-- given
  (hc : 1 < c.natAbs ∨ 1 < h.natAbs) :
-- imply
  bc57_pt c h ∉ bc61_boxAround 2 1 (bc57_pt 0 0) := by
-- proof
  apply StatMech.Walls.bea_out_O hc

/--
[bea_pin_in](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/beaenclosure.lean)
-/
@[path]
private lemma bea_pin_in_eq
  {c h : ℤ}
-- given
  (hc : (c - 10).natAbs ≤ 1)
  (hh : h.natAbs ≤ 1) :
-- imply
  bc57_pt c h ∈ bc61_boxAround 2 1 (bc57_pt 10 0) := by
-- proof
  apply StatMech.Walls.bea_pin_in hc hh

/--
[bea_wall9](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/beaenclosure.lean)
-/
@[path]
private lemma bea_wall9_eq
  {h : ℤ}
-- given
  (hh : h = 0 ∨ h = 1 ∨ h = -1) :
-- imply
  bc57_pt 9 h ∈ bc61_boxAround 2 1 (bc57_pt 10 0) := by
-- proof
  apply StatMech.Walls.bea_wall9 hh

/--
[bea_pin_out_col0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/beaenclosure.lean)
-/
@[path]
private lemma bea_pin_out_col0_eq
  {h : ℤ} :
-- imply
  bc57_pt 0 h ∉ bc61_boxAround 2 1 (bc57_pt 10 0) := by
-- proof
  apply StatMech.Walls.bea_pin_out_col0

/--
[bea_pin_col_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/beaenclosure.lean)
-/
@[path]
private lemma bea_pin_col_step_eq
  {u v : Site 2}
-- given
  (hu : u 0 ≤ 8)
  (hadj : (openSubgraph 2 (removeSites (bc61_boxAround 2 1 (bc57_pt 10 0)) bea_ce)).Adj u v) :
-- imply
  v 0 ≤ 8 := by
-- proof
  apply StatMech.Walls.bea_pin_col_step hu hadj

/--
[bea_pin_col_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/beaenclosure.lean)
-/
@[path]
private lemma bea_pin_col_inv_eq
  {u y : Site 2}
-- given
  (hu : u 0 ≤ 8)
  (hconn : Connected 2 (removeSites (bc61_boxAround 2 1 (bc57_pt 10 0)) bea_ce) u y) :
-- imply
  y 0 ≤ 8 := by
-- proof
  apply StatMech.Walls.bea_pin_col_inv hu hconn

/--
[bea_pinch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/beaenclosure.lean)
-/
@[path]
private lemma bea_pinch_eq :
-- imply
  ¬ (bc67_contractedLattice bea_ce 1 (bc57_pt 10 0)).Reachable (bc57_pt 0 0) (bc57_pt 12 1) := by
-- proof
  apply StatMech.Walls.bea_pinch

/--
[bea_in_O](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/beaenclosure.lean)
-/
@[path]
private lemma bea_in_O_eq
  {c h : ℤ}
-- given
  (hc : c.natAbs ≤ 1)
  (hh : h.natAbs ≤ 1) :
-- imply
  bc57_pt c h ∈ bc61_boxAround 2 1 (bc57_pt 0 0) := by
-- proof
  apply StatMech.Walls.bea_in_O hc hh

/--
[bea_openAdj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/beaenclosure.lean)
-/
@[path]
private lemma bea_openAdj_eq
  {a b h : ℤ}
-- given
  (hh : h = 0 ∨ h = 1 ∨ h = -1)
  (hab : b = a + 1) :
-- imply
  (openSubgraph 2 bea_ce).Adj (bc57_pt a h) (bc57_pt b h) := by
-- proof
  apply StatMech.Walls.bea_openAdj hh hab

/--
[bea_O_height_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/beaenclosure.lean)
-/
@[path]
private lemma bea_O_height_step_eq
  {hgt : ℤ}
  {u v : Site 2}
-- given
  (hu : u 1 = hgt)
  (hadj : (openSubgraph 2 (removeSites (bc61_boxAround 2 1 (bc57_pt 0 0)) bea_ce)).Adj u v) :
-- imply
  v 1 = hgt := by
-- proof
  apply StatMech.Walls.bea_O_height_step hu hadj

/--
[bea_O_height_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/beaenclosure.lean)
-/
@[path]
private lemma bea_O_height_inv_eq
  {hgt : ℤ}
  {u y : Site 2}
-- given
  (hu : u 1 = hgt)
  (hconn : Connected 2 (removeSites (bc61_boxAround 2 1 (bc57_pt 0 0)) bea_ce) u y) :
-- imply
  y 1 = hgt := by
-- proof
  apply StatMech.Walls.bea_O_height_inv hu hconn

/--
[bea_arm_reach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/beaenclosure.lean)
-/
@[path]
private lemma bea_arm_reach_eq
  {h : ℤ}
  {j : ℕ}
-- given
  (hh : h = 0 ∨ h = 1 ∨ h = -1) :
-- imply
  Connected 2 (removeSites (bc61_boxAround 2 1 (bc57_pt 0 0)) bea_ce) (bc57_pt 2 h) (bc57_pt (2 + (j : ℤ)) h) := by
-- proof
  apply StatMech.Walls.bea_arm_reach hh j

/--
[bea_arm_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/beaenclosure.lean)
-/
@[path]
private lemma bea_arm_infinite_eq
  {h : ℤ}
-- given
  (hh : h = 0 ∨ h = 1 ∨ h = -1) :
-- imply
  (cluster 2 (removeSites (bc61_boxAround 2 1 (bc57_pt 0 0)) bea_ce) (bc57_pt 2 h)).Infinite := by
-- proof
  apply StatMech.Walls.bea_arm_infinite hh

/--
[bea_arm_disc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/beaenclosure.lean)
-/
@[path]
private lemma bea_arm_disc_eq
  {h h' : ℤ}
-- given
  (hne : h ≠ h') :
-- imply
  ¬ Connected 2 (removeSites (bc61_boxAround 2 1 (bc57_pt 0 0)) bea_ce) (bc57_pt 2 h) (bc57_pt 2 h') := by
-- proof
  apply StatMech.Walls.bea_arm_disc hne

/--
[bea_horiz_from0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/beaenclosure.lean)
-/
@[path]
private lemma bea_horiz_from0_eq
  {h : ℤ}
  {n : ℤ}
-- given
  (hh : h = 0 ∨ h = 1 ∨ h = -1) :
-- imply
  Connected 2 bea_ce (bc57_pt 0 h) (bc57_pt n h) := by
-- proof
  apply StatMech.Walls.bea_horiz_from0 hh n

/--
[bea_O_to_arm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/beaenclosure.lean)
-/
@[path]
private lemma bea_O_to_arm_eq
  {h : ℤ}
-- given
  (hh : h = 0 ∨ h = 1 ∨ h = -1) :
-- imply
  Connected 2 bea_ce (bc57_pt 0 0) (bc57_pt 2 h) := by
-- proof
  apply StatMech.Walls.bea_O_to_arm hh

/--
[bea_genuineTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/beaenclosure.lean)
-/
@[path]
private lemma bea_genuineTrif_eq :
-- imply
  btr_IsGenuineCoarseTrif bea_ce 1 (bc57_pt 0 0) := by
-- proof
  apply StatMech.Walls.bea_genuineTrif

/--
[bea_gnTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/beaenclosure.lean)
-/
@[path]
private lemma bea_gnTrif_eq :
-- imply
  bc67_IsGnTrifurcation bea_ce 1 (bc57_pt 0 0) := by
-- proof
  apply StatMech.Walls.bea_gnTrif

/--
[bea_arm_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/beaenclosure.lean)
-/
@[path]
private lemma bea_arm_zero_eq :
-- imply
  bea_arm 0 = bc57_pt 12 1 := by
-- proof
  apply StatMech.Walls.bea_arm_zero

/--
[bea_arm_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/beaenclosure.lean)
-/
@[path]
private lemma bea_arm_one_eq :
-- imply
  bea_arm 1 = bc57_pt 10 0 := by
-- proof
  apply StatMech.Walls.bea_arm_one

/--
[bea_repRoute_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/beaenclosure.lean)
-/
@[path]
private lemma bea_repRoute_false_eq :
-- imply
  ¬ bcr_RepRoute bea_ce 1 (bc57_pt 0 0) bea_arm := by
-- proof
  apply StatMech.Walls.bea_repRoute_false

/--
[bea_genuineTrif_entry_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/beaenclosure.lean)
-/
@[path]
private lemma bea_genuineTrif_entry_false_eq :
-- imply
  btr_IsGenuineCoarseTrif bea_ce 1 (bc57_pt 0 0) ∧ ¬ (bc67_contractedLattice bea_ce 1 (bea_arm 1)).Reachable (bc57_pt 0 0) (bea_arm 0) ∧ ¬ bcr_RepRoute bea_ce 1 (bc57_pt 0 0) bea_arm := by
-- proof
  apply StatMech.Walls.bea_genuineTrif_entry_false


-- created on 2026-10-23
