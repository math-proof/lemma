import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.JordanIsCyclesCount.Part5
open SimpleGraph Set StatMech StatMech.Lattice


/--
[jic_edge_at_q_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanIsCyclesCount.lean)
-/
@[path]
private lemma jic_edge_at_q_not_mem_eq
  {G : SimpleGraph (Site 2)}
  {q : Site 2}
  {u v : Site 2}
-- given
  (hfree : ∀ w, ¬ G.Adj q w)
  (hq : u = q ∨ v = q) :
-- imply
  s(u, v) ∉ G.edgeSet := by
-- proof
  apply StatMech.Lattice.jic_edge_at_q_not_mem G hfree hq

/--
[jic_adj_NE_NW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanIsCyclesCount.lean)
-/
@[path]
private lemma jic_adj_NE_NW_eq
  {a b : ℤ} :
-- imply
  (hypercubicLattice 2).Adj ![a, b] ![a - 1, b] := by
-- proof
  apply StatMech.Lattice.jic_adj_NE_NW a b

/--
[jic_adj_NW_SW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanIsCyclesCount.lean)
-/
@[path]
private lemma jic_adj_NW_SW_eq
  {a b : ℤ} :
-- imply
  (hypercubicLattice 2).Adj ![a - 1, b] ![a - 1, b - 1] := by
-- proof
  apply StatMech.Lattice.jic_adj_NW_SW a b

/--
[jic_adj_SW_SE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanIsCyclesCount.lean)
-/
@[path]
private lemma jic_adj_SW_SE_eq
  {a b : ℤ} :
-- imply
  (hypercubicLattice 2).Adj ![a - 1, b - 1] ![a, b - 1] := by
-- proof
  apply StatMech.Lattice.jic_adj_SW_SE a b

/--
[jic_adj_SE_NE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanIsCyclesCount.lean)
-/
@[path]
private lemma jic_adj_SE_NE_eq
  {a b : ℤ} :
-- imply
  (hypercubicLattice 2).Adj ![a, b - 1] ![a, b] := by
-- proof
  apply StatMech.Lattice.jic_adj_SE_NE a b

/--
[jic_shared_NE_NW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanIsCyclesCount.lean)
-/
@[path]
private lemma jic_shared_NE_NW_eq
  {a b : ℤ} :
-- imply
  sharedPrimalEdge ![a, b] ![a - 1, b] = s(![a, b], ![a, b + 1]) := by
-- proof
  apply StatMech.Lattice.jic_shared_NE_NW a b

/--
[jic_shared_NW_SW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanIsCyclesCount.lean)
-/
@[path]
private lemma jic_shared_NW_SW_eq
  {a b : ℤ} :
-- imply
  sharedPrimalEdge ![a - 1, b] ![a - 1, b - 1] = s(![a - 1, b], ![a, b]) := by
-- proof
  apply StatMech.Lattice.jic_shared_NW_SW a b

/--
[jic_shared_SW_SE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanIsCyclesCount.lean)
-/
@[path]
private lemma jic_shared_SW_SE_eq
  {a b : ℤ} :
-- imply
  sharedPrimalEdge ![a - 1, b - 1] ![a, b - 1] = s(![a, b - 1], ![a, b]) := by
-- proof
  apply StatMech.Lattice.jic_shared_SW_SE a b

/--
[jic_shared_SE_NE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanIsCyclesCount.lean)
-/
@[path]
private lemma jic_shared_SE_NE_eq
  {a b : ℤ} :
-- imply
  sharedPrimalEdge ![a, b - 1] ![a, b] = s(![a, b], ![a + 1, b]) := by
-- proof
  apply StatMech.Lattice.jic_shared_SE_NE a b

/--
[jic_faces_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanIsCyclesCount.lean)
-/
@[path]
private lemma jic_faces_distinct_eq
  {a b : ℤ} :
-- imply
  (![a, b] : Site 2) ≠ ![a - 1, b] ∧ (![a, b] : Site 2) ≠ ![a - 1, b - 1] ∧ (![a, b] : Site 2) ≠ ![a, b - 1] ∧ (![a - 1, b] : Site 2) ≠ ![a - 1, b - 1] ∧ (![a - 1, b] : Site 2) ≠ ![a, b - 1] ∧ (![a - 1, b - 1] : Site 2) ≠ ![a, b - 1] := by
-- proof
  apply StatMech.Lattice.jic_faces_distinct a b

/--
[jic_pres_NE_NW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanIsCyclesCount.lean)
-/
@[path]
private lemma jic_pres_NE_NW_eq
  {G : SimpleGraph (Site 2)}
  {a b : ℤ}
-- given
  (hfree : ∀ w, ¬ G.Adj ![a, b] w) :
-- imply
  (whb_faceRegion G).Adj ![a, b] ![a - 1, b] := by
-- proof
  apply StatMech.Lattice.jic_pres_NE_NW G a b hfree

/--
[jic_pres_NW_SW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanIsCyclesCount.lean)
-/
@[path]
private lemma jic_pres_NW_SW_eq
  {G : SimpleGraph (Site 2)}
  {a b : ℤ}
-- given
  (hfree : ∀ w, ¬ G.Adj ![a, b] w) :
-- imply
  (whb_faceRegion G).Adj ![a - 1, b] ![a - 1, b - 1] := by
-- proof
  apply StatMech.Lattice.jic_pres_NW_SW G a b hfree

/--
[jic_pres_SW_SE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanIsCyclesCount.lean)
-/
@[path]
private lemma jic_pres_SW_SE_eq
  {G : SimpleGraph (Site 2)}
  {a b : ℤ}
-- given
  (hfree : ∀ w, ¬ G.Adj ![a, b] w) :
-- imply
  (whb_faceRegion G).Adj ![a - 1, b - 1] ![a, b - 1] := by
-- proof
  apply StatMech.Lattice.jic_pres_SW_SE G a b hfree

/--
[jic_pres_SE_NE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanIsCyclesCount.lean)
-/
@[path]
private lemma jic_pres_SE_NE_eq
  {G : SimpleGraph (Site 2)}
  {a b : ℤ}
-- given
  (hfree : ∀ w, ¬ G.Adj ![a, b] w) :
-- imply
  (whb_faceRegion G).Adj ![a, b - 1] ![a, b] := by
-- proof
  apply StatMech.Lattice.jic_pres_SE_NE G a b hfree

/--
[jic_surv_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanIsCyclesCount.lean)
-/
@[path]
private lemma jic_surv_reachable_eq
  {G : SimpleGraph (Site 2)}
  {e : Sym2 (Site 2)}
  {u v : Site 2}
-- given
  (hadj : (whb_faceRegion G).Adj u v)
  (hne : s(u, v) ≠ e) :
-- imply
  ((whb_faceRegion G).deleteEdges {e}).Reachable u v := by
-- proof
  apply StatMech.Lattice.jic_surv_reachable G e hadj hne

/--
[jic_quad_edge_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanIsCyclesCount.lean)
-/
@[path]
private lemma jic_quad_edge_ne_eq
  {u₁ v₁ u₂ v₂ : Site 2}
-- given
  (h : ¬ ((u₁ = u₂ ∧ v₁ = v₂) ∨ (u₁ = v₂ ∧ v₁ = u₂))) :
-- imply
  s(u₁, v₁) ≠ s(u₂, v₂) := by
-- proof
  apply StatMech.Lattice.jic_quad_edge_ne h

/--
[jic_dangling_east](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanIsCyclesCount.lean)
-/
@[path]
private lemma jic_dangling_east_eq
  {G : SimpleGraph (Site 2)}
  {a b : ℤ}
-- given
  (hfree : ∀ w, ¬ G.Adj ![a, b] w) :
-- imply
  ((whb_faceRegion G).deleteEdges {s((![a, b] : Site 2), ![a, b - 1])}).Reachable ![a, b] ![a, b - 1] := by
-- proof
  apply StatMech.Lattice.jic_dangling_east G a b hfree

/--
[jic_dangling_north](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanIsCyclesCount.lean)
-/
@[path]
private lemma jic_dangling_north_eq
  {G : SimpleGraph (Site 2)}
  {a b : ℤ}
-- given
  (hfree : ∀ w, ¬ G.Adj ![a, b] w) :
-- imply
  ((whb_faceRegion G).deleteEdges {s((![a, b] : Site 2), ![a - 1, b])}).Reachable ![a, b] ![a - 1, b] := by
-- proof
  apply StatMech.Lattice.jic_dangling_north G a b hfree

/--
[jic_dangling_west](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanIsCyclesCount.lean)
-/
@[path]
private lemma jic_dangling_west_eq
  {G : SimpleGraph (Site 2)}
  {a b : ℤ}
-- given
  (hfree : ∀ w, ¬ G.Adj ![a, b] w) :
-- imply
  ((whb_faceRegion G).deleteEdges {s((![a - 1, b] : Site 2), ![a - 1, b - 1])}).Reachable ![a - 1, b] ![a - 1, b - 1] := by
-- proof
  apply StatMech.Lattice.jic_dangling_west G a b hfree

/--
[jic_dangling_south](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanIsCyclesCount.lean)
-/
@[path]
private lemma jic_dangling_south_eq
  {G : SimpleGraph (Site 2)}
  {a b : ℤ}
-- given
  (hfree : ∀ w, ¬ G.Adj ![a, b] w) :
-- imply
  ((whb_faceRegion G).deleteEdges {s((![a - 1, b - 1] : Site 2), ![a, b - 1])}).Reachable ![a - 1, b - 1] ![a, b - 1] := by
-- proof
  apply StatMech.Lattice.jic_dangling_south G a b hfree

/--
[jic_dangling_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanIsCyclesCount.lean)
-/
@[path]
private lemma jic_dangling_bridge_eq
  {G : SimpleGraph (Site 2)}
  {p q : Site 2}
-- given
  (hfree : ∀ w, ¬ G.Adj q w)
  (hpq : (hypercubicLattice 2).Adj p q) :
-- imply
  ∃ f0 g0 : Site 2, (hypercubicLattice 2).Adj f0 g0 ∧ sharedPrimalEdge f0 g0 = s(p, q) ∧ ((whb_faceRegion G).deleteEdges {s(f0, g0)}).Reachable f0 g0 := by
-- proof
  apply StatMech.Lattice.jic_dangling_bridge G hfree hpq

/--
[jic_pushGraph_sup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanIsCyclesCount.lean)
-/
@[path]
private lemma jic_pushGraph_sup_eq
  {P : PlanarZ2Subgraph}
  {A B : SimpleGraph P.V} :
-- imply
  jei_pushGraph P (A ⊔ B) = jei_pushGraph P A ⊔ jei_pushGraph P B := by
-- proof
  apply StatMech.Lattice.jic_pushGraph_sup P A B

/--
[jic_emb_free_of_isolated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanIsCyclesCount.lean)
-/
@[path]
private lemma jic_emb_free_of_isolated_eq
  {P : PlanarZ2Subgraph}
  {H : SimpleGraph P.V}
  {x : P.V}
-- given
  (hiso : ∀ w, ¬ H.Adj x w) :
-- imply
  ∀ w, ¬ (jei_pushGraph P H).Adj (P.emb x) w := by
-- proof
  apply StatMech.Lattice.jic_emb_free_of_isolated P H hiso

/--
[jic_tc_sup_edge_keep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanIsCyclesCount.lean)
-/
@[path]
private lemma jic_tc_sup_edge_keep_eq
  {P : PlanarZ2Subgraph}
  {H : SimpleGraph P.V}
  {x z : P.V}
-- given
  (hxz : x ≠ z)
  (hadjG : (hypercubicLattice 2).Adj (P.emb x) (P.emb z))
  (hiso : ∀ w, ¬ H.Adj x w) :
-- imply
  jic_tc P (H ⊔ edge x z) = jic_tc P H := by
-- proof
  apply StatMech.Lattice.jic_tc_sup_edge_keep P H hxz hadjG hiso

/--
[jic_addWalk_tc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanIsCyclesCount.lean)
-/
@[path]
private lemma jic_addWalk_tc_eq
  {P : PlanarZ2Subgraph} :
-- imply
  ∀ {x y : P.V} (q : P.G.Walk x y) (H : SimpleGraph P.V), q.IsPath → (∀ u ∈ q.support, ∀ w, ¬ H.Adj u w) → jic_tc P (H ⊔ q.toSubgraph.spanningCoe) = jic_tc P H := by
-- proof
  apply StatMech.Lattice.jic_addWalk_tc P

/--
[jic_isCycles_closedContour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanIsCyclesCount.lean)
-/
@[path]
private lemma jic_isCycles_closedContour_eq
  {P : PlanarZ2Subgraph}
  {K : SimpleGraph P.V}
  [DecidableRel K.Adj]
-- given
  (hKle : K ≤ P.G)
  (hcyc : K.IsCycles) :
-- imply
  jce_ClosedContour (jei_pushGraph P K).edgeSet := by
-- proof
  apply StatMech.Lattice.jic_isCycles_closedContour P K hKle hcyc

/--
[jic_tc_close_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanIsCyclesCount.lean)
-/
@[path]
private lemma jic_tc_close_edge_eq
  {P : PlanarZ2Subgraph}
  {Kq : SimpleGraph P.V}
  [DecidableRel Kq.Adj]
  {v z : P.V}
-- given
  (hKqle : Kq ≤ P.G)
  (hadjG : P.G.Adj v z)
  (hnotKq : ¬ Kq.Adj v z)
  (hreach : Kq.Reachable v z)
  (hccK : jce_ClosedContour (jei_pushGraph P (Kq ⊔ edge v z)).edgeSet) :
-- imply
  jic_tc P (Kq ⊔ edge v z) = jic_tc P Kq + 1 := by
-- proof
  apply StatMech.Lattice.jic_tc_close_edge P Kq hKqle hadjG hnotKq hreach hccK

/--
[jic_tc_deleteCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanIsCyclesCount.lean)
-/
@[path]
private lemma jic_tc_deleteCycle_eq
  {P : PlanarZ2Subgraph}
  {K : SimpleGraph P.V}
  [DecidableRel K.Adj]
  {v : P.V}
  {p : K.Walk v v}
-- given
  (hKle : K ≤ P.G)
  (hcyc : K.IsCycles)
  (hp : p.IsCycle) :
-- imply
  jic_tc P K = jic_tc P (K.deleteEdges p.toSubgraph.edgeSet) + 1 := by
-- proof
  apply StatMech.Lattice.jic_tc_deleteCycle P K hKle hcyc p hp

/--
[jic_tc_eq_faceCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanIsCyclesCount.lean)
-/
@[path]
private lemma jic_tc_eq_faceCount_eq
  {P : PlanarZ2Subgraph} :
-- imply
  ∀ (K : SimpleGraph P.V), K ≤ P.G → K.IsCycles → jic_tc P K = faceCount K := by
-- proof
  apply StatMech.Lattice.jic_tc_eq_faceCount P

/--
[jic_total_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanIsCyclesCount.lean)
-/
@[path]
private lemma jic_total_count_eq
  {P : PlanarZ2Subgraph}
-- given
  (hcyc : P.G.IsCycles) :
-- imply
  Nat.card (whb_faceRegion (imageGraph P)).ConnectedComponent = faceCount P.G := by
-- proof
  apply StatMech.Lattice.jic_total_count P hcyc

/--
[jic_faithfulRegionCount_eq_nullity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanIsCyclesCount.lean)
-/
@[path]
private lemma jic_faithfulRegionCount_eq_nullity_eq
  {P : PlanarZ2Subgraph}
-- given
  (hcyc : P.G.IsCycles) :
-- imply
  whc_faithfulRegionCount P = nullity P.G := by
-- proof
  apply StatMech.Lattice.jic_faithfulRegionCount_eq_nullity P hcyc

/--
[jic_faithfulDiscreteJordan](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanIsCyclesCount.lean)
-/
@[path]
private lemma jic_faithfulDiscreteJordan_eq
  {P : PlanarZ2Subgraph}
-- given
  (hcyc : P.G.IsCycles) :
-- imply
  whc_FaithfulDiscreteJordan P := by
-- proof
  apply StatMech.Lattice.jic_faithfulDiscreteJordan P hcyc

/--
[jic_cyc4_isCycles](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanIsCyclesCount.lean)
-/
@[path]
private lemma jic_cyc4_isCycles_eq :
-- imply
  jbc_cyc4.IsCycles := by
-- proof
  apply StatMech.Lattice.jic_cyc4_isCycles

/--
[jic_faithfulDiscreteJordan_unitSquare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanIsCyclesCount.lean)
-/
@[path]
private lemma jic_faithfulDiscreteJordan_unitSquare_eq :
-- imply
  whc_FaithfulDiscreteJordan jbc_Pce := by
-- proof
  apply StatMech.Lattice.jic_faithfulDiscreteJordan_unitSquare

/--
[jic_unitSquare_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanIsCyclesCount.lean)
-/
@[path]
private lemma jic_unitSquare_count_eq :
-- imply
  whc_faithfulRegionCount jbc_Pce = 1 := by
-- proof
  apply StatMech.Lattice.jic_unitSquare_count

/--
[jic_twoSq_emb_inj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanIsCyclesCount.lean)
-/
@[path]
private lemma jic_twoSq_emb_inj_eq :
-- imply
  Function.Injective jic_twoSq_emb := by
-- proof
  apply StatMech.Lattice.jic_twoSq_emb_inj

/--
[jic_twoSq_G_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanIsCyclesCount.lean)
-/
@[path]
private lemma jic_twoSq_G_adj_eq
  {i j : Fin 8} :
-- imply
  jic_twoSq_G.Adj i j ↔ jic_twoSq_rel i j := by
-- proof
  apply StatMech.Lattice.jic_twoSq_G_adj i j

/--
[jic_twoSq_isSub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanIsCyclesCount.lean)
-/
@[path]
private lemma jic_twoSq_isSub_eq :
-- imply
  ∀ ⦃i j : Fin 8⦄, jic_twoSq_G.Adj i j → (hypercubicLattice 2).Adj (jic_twoSq_emb i) (jic_twoSq_emb j) := by
-- proof
  apply StatMech.Lattice.jic_twoSq_isSub

/--
[jic_twoSq_isCycles](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanIsCyclesCount.lean)
-/
@[path]
private lemma jic_twoSq_isCycles_eq :
-- imply
  jic_twoSq_P.G.IsCycles := by
-- proof
  apply StatMech.Lattice.jic_twoSq_isCycles

/--
[jic_faithfulDiscreteJordan_twoSquares](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanIsCyclesCount.lean)
-/
@[path]
private lemma jic_faithfulDiscreteJordan_twoSquares_eq :
-- imply
  whc_FaithfulDiscreteJordan jic_twoSq_P := by
-- proof
  apply StatMech.Lattice.jic_faithfulDiscreteJordan_twoSquares


-- created on 2026-10-23
