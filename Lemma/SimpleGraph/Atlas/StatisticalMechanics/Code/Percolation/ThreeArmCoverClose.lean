import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Percolation.ThreeArmCoverClose
open Set SimpleGraph Finset MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[tac_not_threeArmCover_of_fourArm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ThreeArmCoverClose.lean)
-/
@[path]
private lemma tac_not_threeArmCover_of_fourArm_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {y : Site d}
  {c : Fin 4 → Site d}
-- given
  (hybox : y ∈ box d n)
  (htri : IsTrifurcation d ω y)
  (hconn : ∀ k, Connected d ω y (c k))
  (hne : ∀ k, y ≠ c k)
  (hdis : ∀ k l, k ≠ l → ¬ Connected d (removeSite y ω) (c k) (c l)) :
-- imply
  ¬ fcc_ThreeArmCover ω n := by
-- proof
  apply StatMech.Percolation.tac_not_threeArmCover_of_fourArm ω n hybox htri c hconn hne hdis

/--
[tac_plus_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ThreeArmCoverClose.lean)
-/
@[path]
private lemma tac_plus_mk_eq
  {d : ℕ}
  {x y : Site 2} :
-- imply
  tac_plus s(x, y) = ((decide (x 1 = 0 ∧ y 1 = 0)) || (decide (x 0 = 0 ∧ y 0 = 0))) := by
-- proof
  apply StatMech.Percolation.tac_plus_mk x y

/--
[tac_isOpenEdge_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ThreeArmCoverClose.lean)
-/
@[path]
private lemma tac_isOpenEdge_iff_eq
  {d : ℕ}
  {x y : Site 2} :
-- imply
  IsOpenEdge 2 tac_plus x y ↔ (hypercubicLattice 2).Adj x y ∧ ((x 1 = 0 ∧ y 1 = 0) ∨ (x 0 = 0 ∧ y 0 = 0)) := by
-- proof
  apply StatMech.Percolation.tac_isOpenEdge_iff x y

/--
[tac_ray_east](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ThreeArmCoverClose.lean)
-/
@[path]
private lemma tac_ray_east_eq
  {d : ℕ} :
-- imply
  tac_ray ![1, 0] = 1 := by
-- proof
  apply StatMech.Percolation.tac_ray_east

/--
[tac_ray_west](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ThreeArmCoverClose.lean)
-/
@[path]
private lemma tac_ray_west_eq
  {d : ℕ} :
-- imply
  tac_ray ![-1, 0] = 2 := by
-- proof
  apply StatMech.Percolation.tac_ray_west

/--
[tac_ray_north](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ThreeArmCoverClose.lean)
-/
@[path]
private lemma tac_ray_north_eq
  {d : ℕ} :
-- imply
  tac_ray ![0, 1] = 3 := by
-- proof
  apply StatMech.Percolation.tac_ray_north

/--
[tac_ray_south](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ThreeArmCoverClose.lean)
-/
@[path]
private lemma tac_ray_south_eq
  {d : ℕ} :
-- imply
  tac_ray ![0, -1] = 4 := by
-- proof
  apply StatMech.Percolation.tac_ray_south

/--
[tac_ray_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ThreeArmCoverClose.lean)
-/
@[path]
private lemma tac_ray_invariant_eq
  {d : ℕ}
  {x y : Site 2}
-- given
  (h : IsOpenEdge 2 (removeSite (0 : Site 2) tac_plus) x y) :
-- imply
  tac_ray x = tac_ray y := by
-- proof
  apply StatMech.Percolation.tac_ray_invariant h

/--
[tac_ray_const_of_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ThreeArmCoverClose.lean)
-/
@[path]
private lemma tac_ray_const_of_connected_eq
  {d : ℕ}
  {x y : Site 2}
-- given
  (h : Connected 2 (removeSite (0 : Site 2) tac_plus) x y) :
-- imply
  tac_ray x = tac_ray y := by
-- proof
  apply StatMech.Percolation.tac_ray_const_of_connected h

/--
[tac_disconnected_of_ne_ray](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ThreeArmCoverClose.lean)
-/
@[path]
private lemma tac_disconnected_of_ne_ray_eq
  {d : ℕ}
  {x y : Site 2}
-- given
  (h : tac_ray x ≠ tac_ray y) :
-- imply
  ¬ Connected 2 (removeSite (0 : Site 2) tac_plus) x y := by
-- proof
  apply StatMech.Percolation.tac_disconnected_of_ne_ray h

/--
[tac_conn_east](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ThreeArmCoverClose.lean)
-/
@[path]
private lemma tac_conn_east_eq
  {d : ℕ}
  {k : ℕ} :
-- imply
  Connected 2 tac_plus ![1, 0] ![(k : ℤ) + 1, 0] := by
-- proof
  apply StatMech.Percolation.tac_conn_east k

/--
[tac_conn_west](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ThreeArmCoverClose.lean)
-/
@[path]
private lemma tac_conn_west_eq
  {d : ℕ}
  {k : ℕ} :
-- imply
  Connected 2 tac_plus ![-1, 0] ![-((k : ℤ) + 1), 0] := by
-- proof
  apply StatMech.Percolation.tac_conn_west k

/--
[tac_conn_north](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ThreeArmCoverClose.lean)
-/
@[path]
private lemma tac_conn_north_eq
  {d : ℕ}
  {k : ℕ} :
-- imply
  Connected 2 tac_plus ![0, 1] ![0, (k : ℤ) + 1] := by
-- proof
  apply StatMech.Percolation.tac_conn_north k

/--
[tac_east_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ThreeArmCoverClose.lean)
-/
@[path]
private lemma tac_east_infinite_eq
  {d : ℕ} :
-- imply
  (cluster 2 tac_plus ![1, 0]).Infinite := by
-- proof
  apply StatMech.Percolation.tac_east_infinite

/--
[tac_west_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ThreeArmCoverClose.lean)
-/
@[path]
private lemma tac_west_infinite_eq
  {d : ℕ} :
-- imply
  (cluster 2 tac_plus ![-1, 0]).Infinite := by
-- proof
  apply StatMech.Percolation.tac_west_infinite

/--
[tac_north_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ThreeArmCoverClose.lean)
-/
@[path]
private lemma tac_north_infinite_eq
  {d : ℕ} :
-- imply
  (cluster 2 tac_plus ![0, 1]).Infinite := by
-- proof
  apply StatMech.Percolation.tac_north_infinite

/--
[tac_origin_east](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ThreeArmCoverClose.lean)
-/
@[path]
private lemma tac_origin_east_eq
  {d : ℕ} :
-- imply
  Connected 2 tac_plus (0 : Site 2) ![1, 0] := by
-- proof
  apply StatMech.Percolation.tac_origin_east

/--
[tac_origin_west](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ThreeArmCoverClose.lean)
-/
@[path]
private lemma tac_origin_west_eq
  {d : ℕ} :
-- imply
  Connected 2 tac_plus (0 : Site 2) ![-1, 0] := by
-- proof
  apply StatMech.Percolation.tac_origin_west

/--
[tac_origin_north](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ThreeArmCoverClose.lean)
-/
@[path]
private lemma tac_origin_north_eq
  {d : ℕ} :
-- imply
  Connected 2 tac_plus (0 : Site 2) ![0, 1] := by
-- proof
  apply StatMech.Percolation.tac_origin_north

/--
[tac_origin_south](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ThreeArmCoverClose.lean)
-/
@[path]
private lemma tac_origin_south_eq
  {d : ℕ} :
-- imply
  Connected 2 tac_plus (0 : Site 2) ![0, -1] := by
-- proof
  apply StatMech.Percolation.tac_origin_south

/--
[tac_origin_isTrifurcation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ThreeArmCoverClose.lean)
-/
@[path]
private lemma tac_origin_isTrifurcation_eq
  {d : ℕ} :
-- imply
  IsTrifurcation 2 tac_plus (0 : Site 2) := by
-- proof
  apply StatMech.Percolation.tac_origin_isTrifurcation

/--
[tac_threeArmCover_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ThreeArmCoverClose.lean)
-/
@[path]
private lemma tac_threeArmCover_false_eq
  {d : ℕ} :
-- imply
  ¬ fcc_ThreeArmCover (d := 2) tac_plus 1 := by
-- proof
  apply StatMech.Percolation.tac_threeArmCover_false

/--
[tac_Tcount_le_boundary_of_globalForestArms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ThreeArmCoverClose.lean)
-/
@[path]
private lemma tac_Tcount_le_boundary_of_globalForestArms_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (h : aed_GlobalForestArms ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.tac_Tcount_le_boundary_of_globalForestArms ω n hn h

/--
[tac_burton_keane_bernoulli_of_globalForestArms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ThreeArmCoverClose.lean)
-/
@[path]
private lemma tac_burton_keane_bernoulli_of_globalForestArms_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → aed_GlobalForestArms ω n)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Percolation.tac_burton_keane_bernoulli_of_globalForestArms hd p hp1 hp0 hres htrif


-- created on 2026-10-23
