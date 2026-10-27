import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bxpxpos.Part3
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bxp_cluster_removeSite_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bxpxpos.lean)
-/
@[path]
private lemma bxp_cluster_removeSite_eq_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {b : Site d}
-- given
  (h0 : (0 : Site d) ∉ cluster d ω b) :
-- imply
  cluster d (removeSite 0 ω) b = cluster d ω b := by
-- proof
  apply StatMech.Walls.bxp_cluster_removeSite_eq ω h0

/--
[bxp_infinite_removeSite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bxpxpos.lean)
-/
@[path]
private lemma bxp_infinite_removeSite_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {b : Site d}
-- given
  (h0 : (0 : Site d) ∉ cluster d ω b)
  (hinf : (cluster d ω b).Infinite) :
-- imply
  (cluster d (removeSite 0 ω) b).Infinite := by
-- proof
  apply StatMech.Walls.bxp_infinite_removeSite ω h0 hinf

/--
[bxp_notConnected_removeSite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bxpxpos.lean)
-/
@[path]
private lemma bxp_notConnected_removeSite_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a b : Site d}
-- given
  (h : ¬ Connected d ω a b) :
-- imply
  ¬ Connected d (removeSite 0 ω) a b := by
-- proof
  apply StatMech.Walls.bxp_notConnected_removeSite ω h

/--
[bxp_Y_subset_X](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bxpxpos.lean)
-/
@[path]
private lemma bxp_Y_subset_X_eq
  {d : ℕ} :
-- imply
  bxp_Y ⊆ bmf_X := by
-- proof
  apply StatMech.Walls.bxp_Y_subset_X

/--
[bxp_hXpos_of_fullPos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bxpxpos.lean)
-/
@[path]
private lemma bxp_hXpos_of_fullPos_eq
  {d : ℕ}
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hpos : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 bxp_Y) :
-- imply
  0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 bmf_X := by
-- proof
  apply StatMech.Walls.bxp_hXpos_of_fullPos p hp1 hpos

/--
[bxp_threeMeetBox_subset_iUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bxpxpos.lean)
-/
@[path]
private lemma bxp_threeMeetBox_subset_iUnion_eq
  {d : ℕ}
  {d n : ℕ} :
-- imply
  threeMeetBox d n ⊆ ⋃ x, ⋃ y, ⋃ z, bxp_tripleEvent d n x y z := by
-- proof
  apply StatMech.Walls.bxp_threeMeetBox_subset_iUnion d n

/--
[bxp_exists_triple_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bxpxpos.lean)
-/
@[path]
private lemma bxp_exists_triple_pos_eq
  {d : ℕ}
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (htop : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤}) :
-- imply
  ∃ (n : ℕ) (x y z : Site d), 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (bxp_tripleEvent d n x y z) := by
-- proof
  apply StatMech.Walls.bxp_exists_triple_pos p hp1 htop


-- created on 2026-10-23
