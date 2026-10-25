import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc20mengerroute.Part5
open StatMech.Lattice StatMech.ConfigSpace SimpleGraph StatMech.Percolation StatMech.Percolation.DisjointPaths StatMech StatMech.Walls


/--
[bc20_originBox_coe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc20mengerroute.lean)
-/
@[path]
private lemma bc20_originBox_coe_eq
  {d : ℕ}
  {d m : ℕ} :
-- imply
  (bc20_originBox d m : Site d) = 0 := by
-- proof
  apply StatMech.Walls.bc20_originBox_coe d m

/--
[bc20_hardDir_boxGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc20mengerroute.lean)
-/
@[path]
private lemma bc20_hardDir_boxGraph_eq
  {d : ℕ}
  {d m : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {A B : Set (box d m)} :
-- imply
  bc17_HardDir (bc20_boxGraph d m ω) A B := by
-- proof
  apply StatMech.Walls.bc20_hardDir_boxGraph d m ω A B

/--
[bc20_mapWalk_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc20mengerroute.lean)
-/
@[path]
private lemma bc20_mapWalk_support_eq
  {d : ℕ}
  {d m : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {u v : box d m}
  {p : (bc20_boxGraph d m ω).Walk u v} :
-- imply
  (bc20_mapWalk d m ω p).support = (p.support).map (Embedding.induce (G := openSubgraph d ω) (box d m)).toHom := by
-- proof
  apply StatMech.Walls.bc20_mapWalk_support d m ω p

/--
[bc20_connected_of_boxWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc20mengerroute.lean)
-/
@[path]
private lemma bc20_connected_of_boxWalk_eq
  {d : ℕ}
  {d m : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {u v : box d m}
  {p : (bc20_boxGraph d m ω).Walk u v} :
-- imply
  Connected d ω (u : Site d) (v : Site d) := by
-- proof
  apply StatMech.Walls.bc20_connected_of_boxWalk d m ω p

/--
[bc20_boxWalk_support_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc20mengerroute.lean)
-/
@[path]
private lemma bc20_boxWalk_support_mem_box_eq
  {d : ℕ}
  {d m : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {u v : box d m}
  {p : (bc20_boxGraph d m ω).Walk u v} :
-- imply
  ∀ z ∈ (bc20_mapWalk d m ω p).support, z ∈ box d m := by
-- proof
  apply StatMech.Walls.bc20_boxWalk_support_mem_box d m ω p

/--
[bc20_edge_removeSite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc20mengerroute.lean)
-/
@[path]
private lemma bc20_edge_removeSite_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : Site d}
-- given
  (hadj : (openSubgraph d ω).Adj x y)
  (hx : x ≠ 0)
  (hy : y ≠ 0) :
-- imply
  (openSubgraph d (removeSite 0 ω)).Adj x y := by
-- proof
  apply StatMech.Walls.bc20_edge_removeSite ω hadj hx hy

/--
[bc20_connected_removeSite_of_avoiding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc20mengerroute.lean)
-/
@[path]
private lemma bc20_connected_removeSite_of_avoiding_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a x : Site d}
  {w : (openSubgraph d ω).Walk a x}
-- given
  (h0 : (0 : Site d) ∉ w.support) :
-- imply
  Connected d (removeSite 0 ω) a x := by
-- proof
  apply StatMech.Walls.bc20_connected_removeSite_of_avoiding ω w h0

/--
[bc20_origin_avoid_of_boxAvoid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc20mengerroute.lean)
-/
@[path]
private lemma bc20_origin_avoid_of_boxAvoid_eq
  {d : ℕ}
  {d m : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {u v : box d m}
  {p : (bc20_boxGraph d m ω).Walk u v}
-- given
  (h : bc20_originBox d m ∉ p.support) :
-- imply
  (0 : Site d) ∉ (bc20_mapWalk d m ω p).support := by
-- proof
  apply StatMech.Walls.bc20_origin_avoid_of_boxAvoid d m ω p h

/--
[bc20_unique_index_through](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc20mengerroute.lean)
-/
@[path]
private lemma bc20_unique_index_through_eq
  {d : ℕ}
  {V : Type u}
  [DecidableEq V]
  {GG : SimpleGraph V}
  {A B : Set V}
  {k : ℕ}
  {F : bc16_DisjointPathFamily GG A B (Fin k)}
  {z₀ : V}
  {i j : Fin k}
-- given
  (hi : z₀ ∈ (F.p i).support)
  (hj : z₀ ∈ (F.p j).support) :
-- imply
  i = j := by
-- proof
  apply StatMech.Walls.bc20_unique_index_through F z₀ hi hj

/--
[bc20_disjointFamily_avoids_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc20mengerroute.lean)
-/
@[path]
private lemma bc20_disjointFamily_avoids_origin_eq
  {d : ℕ}
  {V : Type u}
  [DecidableEq V]
  {GG : SimpleGraph V}
  {A B : Set V}
  {F : bc16_DisjointPathFamily GG A B (Fin 2)}
  {z₀ : V} :
-- imply
  ∃ i : Fin 2, z₀ ∉ (F.p i).support := by
-- proof
  apply StatMech.Walls.bc20_disjointFamily_avoids_origin F z₀

/--
[bc20_origin_avoiding_boxPath_of_min2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc20mengerroute.lean)
-/
@[path]
private lemma bc20_origin_avoiding_boxPath_of_min2_eq
  {d : ℕ}
  {V : Type u}
  [DecidableEq V]
  {GG : SimpleGraph V}
  {d m : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {A B : Set (box d m)}
-- given
  (hmin : ∀ C, bc16_IsSeparator (bc20_boxGraph d m ω) A B C → 2 ≤ C.ncard) :
-- imply
  ∃ (u v : box d m) (p : (bc20_boxGraph d m ω).Walk u v), u ∈ A ∧ v ∈ B ∧ bc20_originBox d m ∉ p.support := by
-- proof
  apply StatMech.Walls.bc20_origin_avoiding_boxPath_of_min2 d m ω hmin

/--
[bc20_connected_removeSite_of_min2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc20mengerroute.lean)
-/
@[path]
private lemma bc20_connected_removeSite_of_min2_eq
  {d : ℕ}
  {V : Type u}
  [DecidableEq V]
  {GG : SimpleGraph V}
  {d m : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {A B : Set (box d m)}
-- given
  (hmin : ∀ C, bc16_IsSeparator (bc20_boxGraph d m ω) A B C → 2 ≤ C.ncard) :
-- imply
  ∃ (u v : box d m), u ∈ A ∧ v ∈ B ∧ Connected d (removeSite 0 ω) (u : Site d) (v : Site d) := by
-- proof
  apply StatMech.Walls.bc20_connected_removeSite_of_min2 d m ω hmin

/--
[bc20_shellReach_at](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc20mengerroute.lean)
-/
@[path]
private lemma bc20_shellReach_at_eq
  {d : ℕ}
  {V : Type u}
  [DecidableEq V]
  {GG : SimpleGraph V}
  {d m R : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hmin : ∀ C, bc16_IsSeparator (bc20_boxGraph d m ω) (bc20_shellV d m R) (bc20_boundaryV d m) C → 2 ≤ C.ncard) :
-- imply
  ∃ (u z : Site d), u ∈ vertexBoundary d R ∧ z ∈ vertexBoundary d m ∧ Connected d (removeSite 0 ω) u z := by
-- proof
  apply StatMech.Walls.bc20_shellReach_at d m R ω hmin

/--
[bc20_exists_shellVertex_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc20mengerroute.lean)
-/
@[path]
private lemma bc20_exists_shellVertex_infinite_eq
  {d : ℕ}
  {V : Type u}
  [DecidableEq V]
  {GG : SimpleGraph V}
  {d R : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hmin : ∀ m : ℕ, ∀ C, bc16_IsSeparator (bc20_boxGraph d m ω) (bc20_shellV d m R) (bc20_boundaryV d m) C → 2 ≤ C.ncard) :
-- imply
  ∃ u ∈ vertexBoundary d R, (cluster d (removeSite 0 ω) u).Infinite := by
-- proof
  apply StatMech.Walls.bc20_exists_shellVertex_infinite d R ω hmin

/--
[bc20_removeSite_cluster_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc20mengerroute.lean)
-/
@[path]
private lemma bc20_removeSite_cluster_ne_eq
  {d : ℕ}
  {V : Type u}
  [DecidableEq V]
  {GG : SimpleGraph V}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a₁ a₂ : Site d}
-- given
  (hne : cluster d ω a₁ ≠ cluster d ω a₂) :
-- imply
  cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₂ := by
-- proof
  apply StatMech.Walls.bc20_removeSite_cluster_ne ω a₁ a₂ hne

/--
[bc20_mengerCore_of_originBranchSurvival](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc20mengerroute.lean)
-/
@[path]
private lemma bc20_mengerCore_of_originBranchSurvival_eq
  {d : ℕ}
  {V : Type u}
  [DecidableEq V]
  {GG : SimpleGraph V}
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : bc20_OriginBranchSurvival d ω) :
-- imply
  MengerCore ω := by
-- proof
  apply StatMech.Walls.bc20_mengerCore_of_originBranchSurvival d ω h

/--
[bc20_mengerRoutingCover_of_originBranchSurvival](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc20mengerroute.lean)
-/
@[path]
private lemma bc20_mengerRoutingCover_of_originBranchSurvival_eq
  {d : ℕ}
  {V : Type u}
  [DecidableEq V]
  {GG : SimpleGraph V}
  {d n : ℕ}
-- given
  (h : ∀ ω ∈ threeMeetBox d n, bc20_OriginBranchSurvival d ω) :
-- imply
  MengerRoutingCover d n := by
-- proof
  apply StatMech.Walls.bc20_mengerRoutingCover_of_originBranchSurvival d n h

/--
[bc20_removeSite_infinite_of_originFree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc20mengerroute.lean)
-/
@[path]
private lemma bc20_removeSite_infinite_of_originFree_eq
  {d : ℕ}
  {V : Type u}
  [DecidableEq V]
  {GG : SimpleGraph V}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a : Site d}
-- given
  (h0 : (0 : Site d) ∉ cluster d ω a)
  (hinf : (cluster d ω a).Infinite) :
-- imply
  (cluster d (removeSite 0 ω) a).Infinite := by
-- proof
  apply StatMech.Walls.bc20_removeSite_infinite_of_originFree ω a h0 hinf

/--
[bc20_originBranchSurvival_of_originFree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc20mengerroute.lean)
-/
@[path]
private lemma bc20_originBranchSurvival_of_originFree_eq
  {d : ℕ}
  {V : Type u}
  [DecidableEq V]
  {GG : SimpleGraph V}
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a₁ a₂ a₃ : Site d}
-- given
  (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
  (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧ (hypercubicLattice d).Adj 0 a₃)
  (hdist : cluster d ω a₁ ≠ cluster d ω a₂ ∧ cluster d ω a₁ ≠ cluster d ω a₃ ∧ cluster d ω a₂ ≠ cluster d ω a₃)
  (h0 : (0 : Site d) ∉ cluster d ω a₁ ∧ (0 : Site d) ∉ cluster d ω a₂ ∧ (0 : Site d) ∉ cluster d ω a₃)
  (hinf : (cluster d ω a₁).Infinite ∧ (cluster d ω a₂).Infinite ∧ (cluster d ω a₃).Infinite) :
-- imply
  bc20_OriginBranchSurvival d ω := by
-- proof
  apply StatMech.Walls.bc20_originBranchSurvival_of_originFree d ω a₁ a₂ a₃ hne hadj hdist h0 hinf


-- created on 2026-10-23
