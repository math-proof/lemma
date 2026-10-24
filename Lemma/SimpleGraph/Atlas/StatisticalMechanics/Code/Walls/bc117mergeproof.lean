import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bc117mergeproof
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc117_cut_forceOpen_boxIncident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc117mergeproof.lean)
-/
@[path]
private lemma bc117_cut_forceOpen_boxIncident_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {W : Finset (Sym2 (Site d))}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hW : ∀ e ∈ W, ∃ t ∈ T, t ∈ e) :
-- imply
  removeSites T (forceOpenFinset W ω) = removeSites T ω := by
-- proof
  apply StatMech.Walls.bc117_cut_forceOpen_boxIncident T W ω hW

/--
[bc117_cut_connected_boxIncident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc117mergeproof.lean)
-/
@[path]
private lemma bc117_cut_connected_boxIncident_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {W : Finset (Sym2 (Site d))}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a b : Site d}
-- given
  (hW : ∀ e ∈ W, ∃ t ∈ T, t ∈ e) :
-- imply
  Connected d (removeSites T (forceOpenFinset W ω)) a b ↔ Connected d (removeSites T ω) a b := by
-- proof
  apply StatMech.Walls.bc117_cut_connected_boxIncident hW

/--
[bc117_cut_cluster_boxIncident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc117mergeproof.lean)
-/
@[path]
private lemma bc117_cut_cluster_boxIncident_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {W : Finset (Sym2 (Site d))}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a : Site d}
-- given
  (hW : ∀ e ∈ W, ∃ t ∈ T, t ∈ e) :
-- imply
  cluster d (removeSites T (forceOpenFinset W ω)) a = cluster d (removeSites T ω) a := by
-- proof
  apply StatMech.Walls.bc117_cut_cluster_boxIncident hW a

/--
[bc117_cut_step_of_notMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc117mergeproof.lean)
-/
@[path]
private lemma bc117_cut_step_of_notMem_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a c : Site d}
-- given
  (hadj : (openSubgraph d ω).Adj a c)
  (ha : a ∉ T)
  (hc : c ∉ T) :
-- imply
  Connected d (removeSites T ω) a c := by
-- proof
  apply StatMech.Walls.bc117_cut_step_of_notMem hadj ha hc

/--
[bc117_ray_cut_reach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc117mergeproof.lean)
-/
@[path]
private lemma bc117_ray_cut_reach_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
  {r : ℕ → Site d}
  {k : ℕ}
-- given
  (hadj : ∀ k, (openSubgraph d ω).Adj (r k) (r (k + 1)))
  (havoid : ∀ k, r k ∉ T) :
-- imply
  Connected d (removeSites T ω) (r 0) (r k) := by
-- proof
  apply StatMech.Walls.bc117_ray_cut_reach hadj havoid k

/--
[bc117_ray_cut_cluster_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc117mergeproof.lean)
-/
@[path]
private lemma bc117_ray_cut_cluster_infinite_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
  {r : ℕ → Site d}
-- given
  (hinj : Function.Injective r)
  (hadj : ∀ k, (openSubgraph d ω).Adj (r k) (r (k + 1)))
  (havoid : ∀ k, r k ∉ T) :
-- imply
  (cluster d (removeSites T ω) (r 0)).Infinite := by
-- proof
  apply StatMech.Walls.bc117_ray_cut_cluster_infinite hinj hadj havoid

/--
[bc117_boxAvoiding_external_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc117mergeproof.lean)
-/
@[path]
private lemma bc117_boxAvoiding_external_infinite_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {v : Site d}
  {T : Finset (Site d)}
-- given
  (hinf : (cluster d ω v).Infinite) :
-- imply
  ∃ b : Site d, Connected d ω v b ∧ b ∉ T ∧ (cluster d (removeSites T ω) b).Infinite := by
-- proof
  apply StatMech.Walls.bc117_boxAvoiding_external_infinite ω hinf T

/--
[bc117_merge_of_boxAdjacentExternalArm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc117mergeproof.lean)
-/
@[path]
private lemma bc117_merge_of_boxAdjacentExternalArm_eq
  {d : ℕ}
  {L n : ℕ}
-- given
  (harm : bc117_BoxAdjacentExternalArm d L n) :
-- imply
  bc115_CoarseTrifMerge d L n := by
-- proof
  apply StatMech.Walls.bc117_merge_of_boxAdjacentExternalArm harm

/--
[bc117_shell_of_walk_into_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc117mergeproof.lean)
-/
@[path]
private lemma bc117_shell_of_walk_into_box_eq
  {d : ℕ}
  {L : ℕ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {b u x : Site 2}
  {w : (openSubgraph 2 ω).Walk u x} :
-- imply
  Connected 2 (removeSites (bc61_boxAround 2 L 0) ω) b u → u ∉ bc61_boxAround 2 L 0 → x ∈ bc61_boxAround 2 L 0 → ∃ s t : Site 2, (openSubgraph 2 ω).Adj s t ∧ t ∈ bc61_boxAround 2 L 0 ∧ Connected 2 (removeSites (bc61_boxAround 2 L 0) ω) b s := by
-- proof
  apply StatMech.Walls.bc117_shell_of_walk_into_box w

/--
[bc117_attach_of_meetsBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc117mergeproof.lean)
-/
@[path]
private lemma bc117_attach_of_meetsBox_eq
  {d : ℕ}
  {L : ℕ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {x x' : Site 2}
-- given
  (hinf : (cluster 2 ω x).Infinite)
  (hx'box : x' ∈ bc61_boxAround 2 L 0)
  (hxx' : cluster 2 ω x = cluster 2 ω x') :
-- imply
  ∃ a : Site 2, (∃ bx ∈ bc61_boxAround 2 L 0, (openSubgraph 2 ω).Adj bx a) ∧ (cluster 2 (removeSites (bc61_boxAround 2 L 0) ω) a).Infinite ∧ cluster 2 ω x = cluster 2 ω a := by
-- proof
  apply StatMech.Walls.bc117_attach_of_meetsBox hinf hx'box hxx'

/--
[bc117_merge_of_clustersMeetBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc117mergeproof.lean)
-/
@[path]
private lemma bc117_merge_of_clustersMeetBox_eq
  {d : ℕ}
  {L n : ℕ}
-- given
  (hmeet : ∀ ω ∈ threeMeetBox 2 n, ∀ x₁ x₂ x₃ : Site 2, x₁ ∈ box 2 n → x₂ ∈ box 2 n → x₃ ∈ box 2 n → (cluster 2 ω x₁).Infinite → (cluster 2 ω x₂).Infinite → (cluster 2 ω x₃).Infinite → cluster 2 ω x₁ ≠ cluster 2 ω x₂ → cluster 2 ω x₁ ≠ cluster 2 ω x₃ → cluster 2 ω x₂ ≠ cluster 2 ω x₃ → ∃ x₁' x₂' x₃' : Site 2, x₁' ∈ bc61_boxAround 2 L 0 ∧ x₂' ∈ bc61_boxAround 2 L 0 ∧ x₃' ∈ bc61_boxAround 2 L 0 ∧ cluster 2 ω x₁ = cluster 2 ω x₁' ∧ cluster 2 ω x₂ = cluster 2 ω x₂' ∧ cluster 2 ω x₃ = cluster 2 ω x₃') :
-- imply
  bc115_CoarseTrifMerge 2 L n := by
-- proof
  apply StatMech.Walls.bc117_merge_of_clustersMeetBox hmeet

/--
[bc117_merge_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc117mergeproof.lean)
-/
@[path]
private lemma bc117_merge_of_le_eq
  {d : ℕ}
  {L n : ℕ}
-- given
  (hnL : n ≤ L) :
-- imply
  bc115_CoarseTrifMerge 2 L n := by
-- proof
  apply StatMech.Walls.bc117_merge_of_le hnL

/--
[bc117_engine_fires_upperLines](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc117mergeproof.lean)
-/
@[path]
private lemma bc117_engine_fires_upperLines_eq
  {d : ℕ}
  {h : ℤ}
  {L : ℕ}
-- given
  (hh : 1 ≤ h) :
-- imply
  ∃ b : Site 2, Connected 2 bc60_upperLines (bc57_pt 0 h) b ∧ b ∉ bc61_boxAround 2 L 0 ∧ (cluster 2 (removeSites (bc61_boxAround 2 L 0) bc60_upperLines) b).Infinite := by
-- proof
  apply StatMech.Walls.bc117_engine_fires_upperLines hh L

/--
[bc117_arm_shape_upperLines](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc117mergeproof.lean)
-/
@[path]
private lemma bc117_arm_shape_upperLines_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  ∃ a₁ a₂ a₃ : Site 2, (∃ b₁ ∈ bc61_boxAround 2 L 0, (openSubgraph 2 bc60_upperLines).Adj b₁ a₁) ∧ (∃ b₂ ∈ bc61_boxAround 2 L 0, (openSubgraph 2 bc60_upperLines).Adj b₂ a₂) ∧ (∃ b₃ ∈ bc61_boxAround 2 L 0, (openSubgraph 2 bc60_upperLines).Adj b₃ a₃) ∧ (cluster 2 (removeSites (bc61_boxAround 2 L 0) bc60_upperLines) a₁).Infinite ∧ (cluster 2 (removeSites (bc61_boxAround 2 L 0) bc60_upperLines) a₂).Infinite ∧ (cluster 2 (removeSites (bc61_boxAround 2 L 0) bc60_upperLines) a₃).Infinite := by
-- proof
  apply StatMech.Walls.bc117_arm_shape_upperLines hL

/--
[bc117_merge_of_clustersMeetOriginBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc117mergeproof.lean)
-/
@[path]
private lemma bc117_merge_of_clustersMeetOriginBox_eq
  {d : ℕ}
  {L n : ℕ}
-- given
  (h : bc117_ClustersMeetOriginBox L n) :
-- imply
  bc115_CoarseTrifMerge 2 L n := by
-- proof
  apply StatMech.Walls.bc117_merge_of_clustersMeetOriginBox h

/--
[bc117_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc117mergeproof.lean)
-/
@[path]
private lemma bc117_status_eq
  {d : ℕ} :
-- imply
  (∀ (T : Finset (Site d)) (W : Finset (Sym2 (Site d))) (ω : ConfigSpace (Sym2 (Site d))), (∀ e ∈ W, ∃ t ∈ T, t ∈ e) → removeSites T (forceOpenFinset W ω) = removeSites T ω) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (v : Site d), (cluster d ω v).Infinite → ∀ T : Finset (Site d), ∃ b : Site d, Connected d ω v b ∧ b ∉ T ∧ (cluster d (removeSites T ω) b).Infinite) ∧ (∀ (T : Finset (Site d)) (ω : ConfigSpace (Sym2 (Site d))) (x y : Site d), cluster d ω x ≠ cluster d ω y → ¬ Connected d (removeSites T ω) x y) ∧ (∀ (L n : ℕ), bc117_ClustersMeetOriginBox L n → bc115_CoarseTrifMerge 2 L n) ∧ (∀ (L n : ℕ), n ≤ L → bc115_CoarseTrifMerge 2 L n) := by
-- proof
  apply StatMech.Walls.bc117_status


-- created on 2026-10-23
