import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc47trifarms.Part6
open Set SimpleGraph Finset MeasureTheory StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc47_R_inj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc47trifarms.lean)
-/
@[path]
private lemma bc47_R_inj_eq
  {d : ℕ} :
-- imply
  Function.Injective bc47_R := by
-- proof
  apply StatMech.Walls.bc47_R_inj

/--
[bc47_x_eq_R0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc47trifarms.lean)
-/
@[path]
private lemma bc47_x_eq_R0_eq
  {d : ℕ} :
-- imply
  bc47_x = bc47_R 0 := by
-- proof
  apply StatMech.Walls.bc47_x_eq_R0

/--
[bc47_armEdge_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc47trifarms.lean)
-/
@[path]
private lemma bc47_armEdge_zero_eq
  {d : ℕ} :
-- imply
  bc47_armEdge 0 = s(bc47_x, bc47_a1) := by
-- proof
  apply StatMech.Walls.bc47_armEdge_zero

/--
[bc47_armEdge_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc47trifarms.lean)
-/
@[path]
private lemma bc47_armEdge_one_eq
  {d : ℕ} :
-- imply
  bc47_armEdge 1 = s(bc47_x, bc47_a2) := by
-- proof
  apply StatMech.Walls.bc47_armEdge_one

/--
[bc47_armEdge_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc47trifarms.lean)
-/
@[path]
private lemma bc47_armEdge_two_eq
  {d : ℕ} :
-- imply
  bc47_armEdge 2 = s(bc47_x, bc47_a3) := by
-- proof
  apply StatMech.Walls.bc47_armEdge_two

/--
[bc47_R_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc47trifarms.lean)
-/
@[path]
private lemma bc47_R_adj_eq
  {d : ℕ}
  {k : ℤ} :
-- imply
  (hypercubicLattice 2).Adj (bc47_R k) (bc47_R (k + 1)) := by
-- proof
  apply StatMech.Walls.bc47_R_adj k

/--
[bc47_x_adj_a1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc47trifarms.lean)
-/
@[path]
private lemma bc47_x_adj_a1_eq
  {d : ℕ} :
-- imply
  (hypercubicLattice 2).Adj bc47_x bc47_a1 := by
-- proof
  apply StatMech.Walls.bc47_x_adj_a1

/--
[bc47_x_adj_a2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc47trifarms.lean)
-/
@[path]
private lemma bc47_x_adj_a2_eq
  {d : ℕ} :
-- imply
  (hypercubicLattice 2).Adj bc47_x bc47_a2 := by
-- proof
  apply StatMech.Walls.bc47_x_adj_a2

/--
[bc47_x_adj_a3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc47trifarms.lean)
-/
@[path]
private lemma bc47_x_adj_a3_eq
  {d : ℕ} :
-- imply
  (hypercubicLattice 2).Adj bc47_x bc47_a3 := by
-- proof
  apply StatMech.Walls.bc47_x_adj_a3

/--
[bc47_armEdge_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc47trifarms.lean)
-/
@[path]
private lemma bc47_armEdge_open_eq
  {d : ℕ}
  {i : Fin 3} :
-- imply
  bc47_fakeConfig (bc47_armEdge i) = true := by
-- proof
  apply StatMech.Walls.bc47_armEdge_open i

/--
[bc47_x_a1_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc47trifarms.lean)
-/
@[path]
private lemma bc47_x_a1_open_eq
  {d : ℕ} :
-- imply
  bc47_fakeConfig s(bc47_x, bc47_a1) = true := by
-- proof
  apply StatMech.Walls.bc47_x_a1_open

/--
[bc47_x_a2_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc47trifarms.lean)
-/
@[path]
private lemma bc47_x_a2_open_eq
  {d : ℕ} :
-- imply
  bc47_fakeConfig s(bc47_x, bc47_a2) = true := by
-- proof
  apply StatMech.Walls.bc47_x_a2_open

/--
[bc47_x_a3_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc47trifarms.lean)
-/
@[path]
private lemma bc47_x_a3_open_eq
  {d : ℕ} :
-- imply
  bc47_fakeConfig s(bc47_x, bc47_a3) = true := by
-- proof
  apply StatMech.Walls.bc47_x_a3_open

/--
[bc47_R_edge_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc47trifarms.lean)
-/
@[path]
private lemma bc47_R_edge_open_eq
  {d : ℕ}
  {k : ℤ}
-- given
  (hk : 0 ≤ k) :
-- imply
  bc47_fakeConfig s(bc47_R k, bc47_R (k + 1)) = true := by
-- proof
  apply StatMech.Walls.bc47_R_edge_open k hk

/--
[bc47_R_edge_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc47trifarms.lean)
-/
@[path]
private lemma bc47_R_edge_connected_eq
  {d : ℕ}
  {k : ℤ}
-- given
  (hk : 0 ≤ k) :
-- imply
  Connected 2 bc47_fakeConfig (bc47_R k) (bc47_R (k + 1)) := by
-- proof
  apply StatMech.Walls.bc47_R_edge_connected k hk

/--
[bc47_x_connected_R](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc47trifarms.lean)
-/
@[path]
private lemma bc47_x_connected_R_eq
  {d : ℕ}
  {m : ℤ}
-- given
  (hm : 0 ≤ m) :
-- imply
  Connected 2 bc47_fakeConfig bc47_x (bc47_R m) := by
-- proof
  apply StatMech.Walls.bc47_x_connected_R m hm

/--
[bc47_x_connected_a1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc47trifarms.lean)
-/
@[path]
private lemma bc47_x_connected_a1_eq
  {d : ℕ} :
-- imply
  Connected 2 bc47_fakeConfig bc47_x bc47_a1 := by
-- proof
  apply StatMech.Walls.bc47_x_connected_a1

/--
[bc47_x_connected_a2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc47trifarms.lean)
-/
@[path]
private lemma bc47_x_connected_a2_eq
  {d : ℕ} :
-- imply
  Connected 2 bc47_fakeConfig bc47_x bc47_a2 := by
-- proof
  apply StatMech.Walls.bc47_x_connected_a2

/--
[bc47_x_connected_a3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc47trifarms.lean)
-/
@[path]
private lemma bc47_x_connected_a3_eq
  {d : ℕ} :
-- imply
  Connected 2 bc47_fakeConfig bc47_x bc47_a3 := by
-- proof
  apply StatMech.Walls.bc47_x_connected_a3

/--
[bc47_R_outside_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc47trifarms.lean)
-/
@[path]
private lemma bc47_R_outside_box_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  bc47_R (n + 1) ∉ box 2 n := by
-- proof
  apply StatMech.Walls.bc47_R_outside_box n

/--
[bc47_a1_ambient_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc47trifarms.lean)
-/
@[path]
private lemma bc47_a1_ambient_infinite_eq
  {d : ℕ} :
-- imply
  (cluster 2 bc47_fakeConfig bc47_a1).Infinite := by
-- proof
  apply StatMech.Walls.bc47_a1_ambient_infinite

/--
[bc47_a2_ambient_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc47trifarms.lean)
-/
@[path]
private lemma bc47_a2_ambient_infinite_eq
  {d : ℕ} :
-- imply
  (cluster 2 bc47_fakeConfig bc47_a2).Infinite := by
-- proof
  apply StatMech.Walls.bc47_a2_ambient_infinite

/--
[bc47_a3_ambient_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc47trifarms.lean)
-/
@[path]
private lemma bc47_a3_ambient_infinite_eq
  {d : ℕ} :
-- imply
  (cluster 2 bc47_fakeConfig bc47_a3).Infinite := by
-- proof
  apply StatMech.Walls.bc47_a3_ambient_infinite

/--
[bc47_arm_not_R_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc47trifarms.lean)
-/
@[path]
private lemma bc47_arm_not_R_edge_eq
  {d : ℕ}
  {a : Site 2}
  {k : ℤ}
-- given
  (ha : a = bc47_a1 ∨ a = bc47_a2 ∨ a = bc47_a3)
  (hk : 0 ≤ k) :
-- imply
  a ∉ s(bc47_R k, bc47_R (k + 1)) := by
-- proof
  apply StatMech.Walls.bc47_arm_not_R_edge a ha k hk

/--
[bc47_arm_isolated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc47trifarms.lean)
-/
@[path]
private lemma bc47_arm_isolated_eq
  {d : ℕ}
  {a : Site 2}
  {y : Site 2}
-- given
  (ha : a = bc47_a1 ∨ a = bc47_a2 ∨ a = bc47_a3) :
-- imply
  ¬ (openSubgraph 2 (removeSite bc47_x bc47_fakeConfig)).Adj a y := by
-- proof
  apply StatMech.Walls.bc47_arm_isolated a ha y

/--
[bc47_arm_removeSite_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc47trifarms.lean)
-/
@[path]
private lemma bc47_arm_removeSite_finite_eq
  {d : ℕ}
  {a : Site 2}
-- given
  (ha : a = bc47_a1 ∨ a = bc47_a2 ∨ a = bc47_a3) :
-- imply
  (cluster 2 (removeSite bc47_x bc47_fakeConfig) a).Finite := by
-- proof
  apply StatMech.Walls.bc47_arm_removeSite_finite a ha

/--
[bc47_arms_removeSite_disconnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc47trifarms.lean)
-/
@[path]
private lemma bc47_arms_removeSite_disconnected_eq
  {d : ℕ} :
-- imply
  ¬ Connected 2 (removeSite bc47_x bc47_fakeConfig) bc47_a1 bc47_a2 ∧ ¬ Connected 2 (removeSite bc47_x bc47_fakeConfig) bc47_a1 bc47_a3 ∧ ¬ Connected 2 (removeSite bc47_x bc47_fakeConfig) bc47_a2 bc47_a3 := by
-- proof
  apply StatMech.Walls.bc47_arms_removeSite_disconnected

/--
[bc47_arms_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc47trifarms.lean)
-/
@[path]
private lemma bc47_arms_distinct_eq
  {d : ℕ} :
-- imply
  bc47_a1 ≠ bc47_a2 ∧ bc47_a1 ≠ bc47_a3 ∧ bc47_a2 ≠ bc47_a3 := by
-- proof
  apply StatMech.Walls.bc47_arms_distinct

/--
[bc47_isTrifurcation_fakeConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc47trifarms.lean)
-/
@[path]
private lemma bc47_isTrifurcation_fakeConfig_eq
  {d : ℕ} :
-- imply
  IsTrifurcation 2 bc47_fakeConfig bc47_x := by
-- proof
  apply StatMech.Walls.bc47_isTrifurcation_fakeConfig

/--
[bc47_isTrifurcation_not_threeRemoveSiteInfiniteArms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc47trifarms.lean)
-/
@[path]
private lemma bc47_isTrifurcation_not_threeRemoveSiteInfiniteArms_eq
  {d : ℕ} :
-- imply
  ∃ (ω : ConfigSpace (Sym2 (Site 2))) (x : Site 2), IsTrifurcation 2 ω x ∧ ∃ a₁ a₂ a₃ : Site 2, (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧ (Connected 2 ω x a₁ ∧ Connected 2 ω x a₂ ∧ Connected 2 ω x a₃) ∧ ((cluster 2 ω a₁).Infinite ∧ (cluster 2 ω a₂).Infinite ∧ (cluster 2 ω a₃).Infinite) ∧ (¬ Connected 2 (removeSite x ω) a₁ a₂ ∧ ¬ Connected 2 (removeSite x ω) a₁ a₃ ∧ ¬ Connected 2 (removeSite x ω) a₂ a₃) ∧ (¬ (cluster 2 (removeSite x ω) a₁).Infinite ∧ ¬ (cluster 2 (removeSite x ω) a₂).Infinite ∧ ¬ (cluster 2 (removeSite x ω) a₃).Infinite) := by
-- proof
  apply StatMech.Walls.bc47_isTrifurcation_not_threeRemoveSiteInfiniteArms

/--
[bc47_removeSite_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc47trifarms.lean)
-/
@[path]
private lemma bc47_removeSite_le_eq
  {d : ℕ}
  {x : Site d}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  removeSite x ω ≤ ω := by
-- proof
  apply StatMech.Walls.bc47_removeSite_le x ω

/--
[bc47_isTrifurcation_of_classical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc47trifarms.lean)
-/
@[path]
private lemma bc47_isTrifurcation_of_classical_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (h : bc47_IsClassicalTrifurcation ω x) :
-- imply
  IsTrifurcation d ω x := by
-- proof
  apply StatMech.Walls.bc47_isTrifurcation_of_classical ω x h

/--
[bc47_only_infinite_neighbour_is_R1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc47trifarms.lean)
-/
@[path]
private lemma bc47_only_infinite_neighbour_is_R1_eq
  {d : ℕ}
  {a : Site 2}
-- given
  (hea : IsOpenEdge 2 bc47_fakeConfig bc47_x a)
  (hia : (cluster 2 (removeSite bc47_x bc47_fakeConfig) a).Infinite) :
-- imply
  a = bc47_R 1 := by
-- proof
  apply StatMech.Walls.bc47_only_infinite_neighbour_is_R1 a hea hia

/--
[bc47_not_classical_fakeConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc47trifarms.lean)
-/
@[path]
private lemma bc47_not_classical_fakeConfig_eq
  {d : ℕ} :
-- imply
  ¬ bc47_IsClassicalTrifurcation bc47_fakeConfig bc47_x := by
-- proof
  apply StatMech.Walls.bc47_not_classical_fakeConfig

/--
[arc_trifArmsRemoveSiteInfinite_of_classical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc47trifarms.lean)
-/
@[path]
private lemma arc_trifArmsRemoveSiteInfinite_of_classical_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hcl : ∀ x, x ∈ box d n → IsTrifurcation d ω x → bc47_IsClassicalTrifurcation ω x) :
-- imply
  arc_TrifArmsRemoveSiteInfinite ω n := by
-- proof
  apply StatMech.Walls.arc_trifArmsRemoveSiteInfinite_of_classical ω n hcl

/--
[bc47_trif_arm_data_of_classical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc47trifarms.lean)
-/
@[path]
private lemma bc47_trif_arm_data_of_classical_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x : Site d}
-- given
  (hcl : ∀ x, x ∈ box d n → IsTrifurcation d ω x → bc47_IsClassicalTrifurcation ω x)
  (hxbox : x ∈ box d n)
  (htri : IsTrifurcation d ω x) :
-- imply
  ∃ (c : Fin 3 → Site d) (zr : Fin 3 → Site d), (∀ i, (openSubgraph d ω).Adj x (c i)) ∧ (∀ i, c i ≠ x) ∧ (¬ Connected d (removeSite x ω) (c 0) (c 1) ∧ ¬ Connected d (removeSite x ω) (c 0) (c 2) ∧ ¬ Connected d (removeSite x ω) (c 1) (c 2)) ∧ (∀ i, zr i ∈ vertexBoundary d (n + 1) ∧ ∃ w : (openSubgraph d (removeSite x ω)).Walk (c i) (zr i), x ∉ w.support) := by
-- proof
  apply StatMech.Walls.bc47_trif_arm_data_of_classical ω n hcl x hxbox htri

/--
[bc47_clawShadow_classical_ok](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc47trifarms.lean)
-/
@[path]
private lemma bc47_clawShadow_classical_ok_eq
  {d : ℕ} :
-- imply
  ∀ c : Fin 10, (c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) → ∃ n₁ n₂ n₃ : Fin 10, (bc46_clawLab c n₁ ≠ bc46_clawLab c n₂ ∧ bc46_clawLab c n₁ ≠ bc46_clawLab c n₃ ∧ bc46_clawLab c n₂ ≠ bc46_clawLab c n₃) ∧ (∃ z₁, bc46_clawLab c z₁ = bc46_clawLab c n₁ ∧ bc47_clawIsArm z₁ = true) ∧ (∃ z₂, bc46_clawLab c z₂ = bc46_clawLab c n₂ ∧ bc47_clawIsArm z₂ = true) ∧ (∃ z₃, bc46_clawLab c z₃ = bc46_clawLab c n₃ ∧ bc47_clawIsArm z₃ = true) := by
-- proof
  apply StatMech.Walls.bc47_clawShadow_classical_ok

/--
[bc47_chainShadow_arms_ok](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc47trifarms.lean)
-/
@[path]
private lemma bc47_chainShadow_arms_ok_eq
  {d : ℕ} :
-- imply
  ∀ c : Fin 8, (c = 1 ∨ c = 2) → ∃ n₁ n₂ n₃ : Fin 8, (bc46_chainLab c n₁ ≠ bc46_chainLab c n₂ ∧ bc46_chainLab c n₁ ≠ bc46_chainLab c n₃ ∧ bc46_chainLab c n₂ ≠ bc46_chainLab c n₃) ∧ (∃ z₁, bc46_chainLab c z₁ = bc46_chainLab c n₁ ∧ bc47_chainIsArm z₁ = true) ∧ (∃ z₂, bc46_chainLab c z₂ = bc46_chainLab c n₂ ∧ bc47_chainIsArm z₂ = true) ∧ (∃ z₃, bc46_chainLab c z₃ = bc46_chainLab c n₃ ∧ bc47_chainIsArm z₃ = true) := by
-- proof
  apply StatMech.Walls.bc47_chainShadow_arms_ok

/--
[bc47_classical_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc47trifarms.lean)
-/
@[path]
private lemma bc47_classical_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  ∀ x, x ∈ box d n → IsTrifurcation d ω x → bc47_IsClassicalTrifurcation ω x := by
-- proof
  apply StatMech.Walls.bc47_classical_of_noTrif ω n hno

/--
[bc47_x_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc47trifarms.lean)
-/
@[path]
private lemma bc47_x_mem_box_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  bc47_x ∈ box 2 n := by
-- proof
  apply StatMech.Walls.bc47_x_mem_box n

/--
[bc47_arc_residue_fails_on_fakeConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc47trifarms.lean)
-/
@[path]
private lemma bc47_arc_residue_fails_on_fakeConfig_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  ¬ arc_TrifArmsRemoveSiteInfinite bc47_fakeConfig n := by
-- proof
  apply StatMech.Walls.bc47_arc_residue_fails_on_fakeConfig n


-- created on 2026-10-23
