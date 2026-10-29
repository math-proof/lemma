import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc59corridors.Part3
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc59_corridors_give_trifurcation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc59corridors.lean)
-/
@[path]
private lemma bc59_corridors_give_trifurcation_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : bc59_DisjointCorridors ω) :
-- imply
  ∃ G : Finset (Sym2 (Site d)), bc47_IsClassicalTrifurcation (forceOpenFinset G ω) 0 := by
-- proof
  apply StatMech.Walls.bc59_corridors_give_trifurcation ω h

/--
[bc59_originTrifModification_of_hasCorridors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc59corridors.lean)
-/
@[path]
private lemma bc59_originTrifModification_of_hasCorridors_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : bc59_HasDisjointCorridors d n) :
-- imply
  bc58_OriginTrifModification d n := by
-- proof
  apply StatMech.Walls.bc59_originTrifModification_of_hasCorridors h

/--
[bc59_burton_keane_bernoulli_of_hasCorridors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc59corridors.lean)
-/
@[path]
private lemma bc59_burton_keane_bernoulli_of_hasCorridors_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : NNReal)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (h : ∀ n : ℕ, bc59_HasDisjointCorridors d n) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc59_burton_keane_bernoulli_of_hasCorridors hd p hp1 hp0 h

/--
[bc59_origin_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc59corridors.lean)
-/
@[path]
private lemma bc59_origin_eq_eq
  {d : ℕ} :
-- imply
  (0 : Site 2) = bc57_pt 0 0 := by
-- proof
  apply StatMech.Walls.bc59_origin_eq

/--
[bc59_pt_eq_origin_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc59corridors.lean)
-/
@[path]
private lemma bc59_pt_eq_origin_iff_eq
  {d : ℕ}
  {a b : ℤ} :
-- imply
  bc57_pt a b = (0 : Site 2) ↔ a = 0 ∧ b = 0 := by
-- proof
  apply StatMech.Walls.bc59_pt_eq_origin_iff

/--
[bc59_corridor_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc59corridors.lean)
-/
@[path]
private lemma bc59_corridor_open_eq
  {d : ℕ} :
-- imply
  (removeSite 0 bc59_omega') s(bc57_pt 0 1, bc57_pt 0 2) = true := by
-- proof
  apply StatMech.Walls.bc59_corridor_open

/--
[bc59_open_edge_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc59corridors.lean)
-/
@[path]
private lemma bc59_open_edge_dichotomy_eq
  {d : ℕ}
  {u v : Site 2}
-- given
  (hopen : (removeSite 0 bc59_omega') s(u, v) = true) :
-- imply
  ((0 : Site 2) ∉ s(u, v)) ∧ ((∃ k m : ℤ, s(u, v) = s(bc57_pt k (2 * m), bc57_pt (k + 1) (2 * m))) ∨ s(u, v) = s(bc57_pt 0 1, bc57_pt 0 2)) := by
-- proof
  apply StatMech.Walls.bc59_open_edge_dichotomy hopen

/--
[bc59_R_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc59corridors.lean)
-/
@[path]
private lemma bc59_R_step_eq
  {d : ℕ}
  {u v : Site 2}
-- given
  (hu0 : u 1 = 0)
  (hu1 : 1 ≤ u 0)
  (hadj : (openSubgraph 2 (removeSite 0 bc59_omega')).Adj u v) :
-- imply
  v 1 = 0 ∧ 1 ≤ v 0 := by
-- proof
  apply StatMech.Walls.bc59_R_step hu0 hu1 hadj

/--
[bc59_L_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc59corridors.lean)
-/
@[path]
private lemma bc59_L_step_eq
  {d : ℕ}
  {u v : Site 2}
-- given
  (hu0 : u 1 = 0)
  (hu1 : u 0 ≤ -1)
  (hadj : (openSubgraph 2 (removeSite 0 bc59_omega')).Adj u v) :
-- imply
  v 1 = 0 ∧ v 0 ≤ -1 := by
-- proof
  apply StatMech.Walls.bc59_L_step hu0 hu1 hadj

/--
[bc59_T_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc59corridors.lean)
-/
@[path]
private lemma bc59_T_step_eq
  {d : ℕ}
  {u v : Site 2}
-- given
  (hu1 : 1 ≤ u 1)
  (hadj : (openSubgraph 2 (removeSite 0 bc59_omega')).Adj u v) :
-- imply
  1 ≤ v 1 := by
-- proof
  apply StatMech.Walls.bc59_T_step hu1 hadj

/--
[bc59_R_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc59corridors.lean)
-/
@[path]
private lemma bc59_R_invariant_eq
  {d : ℕ}
  {u y : Site 2}
-- given
  (hu0 : u 1 = 0)
  (hu1 : 1 ≤ u 0)
  (hconn : Connected 2 (removeSite 0 bc59_omega') u y) :
-- imply
  y 1 = 0 ∧ 1 ≤ y 0 := by
-- proof
  apply StatMech.Walls.bc59_R_invariant hu0 hu1 hconn

/--
[bc59_L_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc59corridors.lean)
-/
@[path]
private lemma bc59_L_invariant_eq
  {d : ℕ}
  {u y : Site 2}
-- given
  (hu0 : u 1 = 0)
  (hu1 : u 0 ≤ -1)
  (hconn : Connected 2 (removeSite 0 bc59_omega') u y) :
-- imply
  y 1 = 0 ∧ y 0 ≤ -1 := by
-- proof
  apply StatMech.Walls.bc59_L_invariant hu0 hu1 hconn

/--
[bc59_T_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc59corridors.lean)
-/
@[path]
private lemma bc59_T_invariant_eq
  {d : ℕ}
  {u y : Site 2}
-- given
  (hu1 : 1 ≤ u 1)
  (hconn : Connected 2 (removeSite 0 bc59_omega') u y) :
-- imply
  1 ≤ y 1 := by
-- proof
  apply StatMech.Walls.bc59_T_invariant hu1 hconn

/--
[bc59_line0_edge_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc59corridors.lean)
-/
@[path]
private lemma bc59_line0_edge_open_eq
  {d : ℕ}
  {k : ℤ}
-- given
  (h0 : (0 : Site 2) ∉ s(bc57_pt k 0, bc57_pt (k + 1) 0)) :
-- imply
  (removeSite 0 bc59_omega') s(bc57_pt k 0, bc57_pt (k + 1) 0) = true := by
-- proof
  apply StatMech.Walls.bc59_line0_edge_open h0

/--
[bc59_line2_edge_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc59corridors.lean)
-/
@[path]
private lemma bc59_line2_edge_open_eq
  {d : ℕ}
  {k : ℤ} :
-- imply
  (removeSite 0 bc59_omega') s(bc57_pt k 2, bc57_pt (k + 1) 2) = true := by
-- proof
  apply StatMech.Walls.bc59_line2_edge_open k

/--
[bc59_R_reach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc59corridors.lean)
-/
@[path]
private lemma bc59_R_reach_eq
  {d : ℕ}
  {j : ℕ} :
-- imply
  Connected 2 (removeSite 0 bc59_omega') (bc57_pt 1 0) (bc57_pt ((j : ℤ) + 1) 0) := by
-- proof
  apply StatMech.Walls.bc59_R_reach j

/--
[bc59_L_reach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc59corridors.lean)
-/
@[path]
private lemma bc59_L_reach_eq
  {d : ℕ}
  {j : ℕ} :
-- imply
  Connected 2 (removeSite 0 bc59_omega') (bc57_pt (-1) 0) (bc57_pt (-((j : ℤ) + 1)) 0) := by
-- proof
  apply StatMech.Walls.bc59_L_reach j

/--
[bc59_T_reach_line2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc59corridors.lean)
-/
@[path]
private lemma bc59_T_reach_line2_eq
  {d : ℕ}
  {j : ℕ} :
-- imply
  Connected 2 (removeSite 0 bc59_omega') (bc57_pt 0 2) (bc57_pt (j : ℤ) 2) := by
-- proof
  apply StatMech.Walls.bc59_T_reach_line2 j

/--
[bc59_T_reach_corridor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc59corridors.lean)
-/
@[path]
private lemma bc59_T_reach_corridor_eq
  {d : ℕ} :
-- imply
  Connected 2 (removeSite 0 bc59_omega') (bc57_pt 0 1) (bc57_pt 0 2) := by
-- proof
  apply StatMech.Walls.bc59_T_reach_corridor

/--
[bc59_pt_outside_box_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc59corridors.lean)
-/
@[path]
private lemma bc59_pt_outside_box_fst_eq
  {d : ℕ}
  {n : ℕ}
  {a b : ℤ}
-- given
  (ha : n < a.natAbs) :
-- imply
  bc57_pt a b ∉ box 2 n := by
-- proof
  apply StatMech.Walls.bc59_pt_outside_box_fst ha

/--
[bc59_R_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc59corridors.lean)
-/
@[path]
private lemma bc59_R_infinite_eq
  {d : ℕ} :
-- imply
  (cluster 2 (removeSite 0 bc59_omega') (bc57_pt 1 0)).Infinite := by
-- proof
  apply StatMech.Walls.bc59_R_infinite

/--
[bc59_L_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc59corridors.lean)
-/
@[path]
private lemma bc59_L_infinite_eq
  {d : ℕ} :
-- imply
  (cluster 2 (removeSite 0 bc59_omega') (bc57_pt (-1) 0)).Infinite := by
-- proof
  apply StatMech.Walls.bc59_L_infinite

/--
[bc59_T_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc59corridors.lean)
-/
@[path]
private lemma bc59_T_infinite_eq
  {d : ℕ} :
-- imply
  (cluster 2 (removeSite 0 bc59_omega') (bc57_pt 0 1)).Infinite := by
-- proof
  apply StatMech.Walls.bc59_T_infinite

/--
[bc59_sep_RL](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc59corridors.lean)
-/
@[path]
private lemma bc59_sep_RL_eq
  {d : ℕ} :
-- imply
  ¬ Connected 2 (removeSite 0 bc59_omega') (bc57_pt 1 0) (bc57_pt (-1) 0) := by
-- proof
  apply StatMech.Walls.bc59_sep_RL

/--
[bc59_sep_RT](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc59corridors.lean)
-/
@[path]
private lemma bc59_sep_RT_eq
  {d : ℕ} :
-- imply
  ¬ Connected 2 (removeSite 0 bc59_omega') (bc57_pt 1 0) (bc57_pt 0 1) := by
-- proof
  apply StatMech.Walls.bc59_sep_RT

/--
[bc59_sep_LT](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc59corridors.lean)
-/
@[path]
private lemma bc59_sep_LT_eq
  {d : ℕ} :
-- imply
  ¬ Connected 2 (removeSite 0 bc59_omega') (bc57_pt (-1) 0) (bc57_pt 0 1) := by
-- proof
  apply StatMech.Walls.bc59_sep_LT

/--
[bc59_arms_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc59corridors.lean)
-/
@[path]
private lemma bc59_arms_distinct_eq
  {d : ℕ} :
-- imply
  bc59_a1 ≠ bc59_a2 ∧ bc59_a1 ≠ bc59_a3 ∧ bc59_a2 ≠ bc59_a3 := by
-- proof
  apply StatMech.Walls.bc59_arms_distinct

/--
[bc59_arms_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc59corridors.lean)
-/
@[path]
private lemma bc59_arms_adj_eq
  {d : ℕ} :
-- imply
  (hypercubicLattice 2).Adj 0 bc59_a1 ∧ (hypercubicLattice 2).Adj 0 bc59_a2 ∧ (hypercubicLattice 2).Adj 0 bc59_a3 := by
-- proof
  apply StatMech.Walls.bc59_arms_adj

/--
[bc59_evenLines_hasDisjointCorridors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc59corridors.lean)
-/
@[path]
private lemma bc59_evenLines_hasDisjointCorridors_eq
  {d : ℕ} :
-- imply
  bc59_DisjointCorridors bc57_evenLines := by
-- proof
  apply StatMech.Walls.bc59_evenLines_hasDisjointCorridors

/--
[bc59_evenLines_originTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc59corridors.lean)
-/
@[path]
private lemma bc59_evenLines_originTrif_eq
  {d : ℕ} :
-- imply
  ∃ G : Finset (Sym2 (Site 2)), bc47_IsClassicalTrifurcation (forceOpenFinset G bc57_evenLines) 0 := by
-- proof
  apply StatMech.Walls.bc59_evenLines_originTrif

/--
[bc59_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc59corridors.lean)
-/
@[path]
private lemma bc59_status_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : NNReal)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p) :
-- imply
  ((∀ n : ℕ, bc59_HasDisjointCorridors d n) → (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1) ∧ (∀ ω : ConfigSpace (Sym2 (Site d)), bc59_DisjointCorridors ω → ∃ G : Finset (Sym2 (Site d)), bc47_IsClassicalTrifurcation (forceOpenFinset G ω) 0) ∧ bc59_DisjointCorridors bc57_evenLines ∧ (∃ G : Finset (Sym2 (Site 2)), bc47_IsClassicalTrifurcation (forceOpenFinset G bc57_evenLines) 0) := by
-- proof
  apply StatMech.Walls.bc59_status hd p hp1 hp0


-- created on 2026-10-23
