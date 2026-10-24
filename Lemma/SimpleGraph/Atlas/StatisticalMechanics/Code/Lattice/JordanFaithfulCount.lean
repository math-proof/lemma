import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.JordanFaithfulCount
open SimpleGraph Set StatMech StatMech.Lattice


/--
[jfc_whb_sup_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFaithfulCount.lean)
-/
@[path]
private lemma jfc_whb_sup_edge_eq
  {G : SimpleGraph (Site 2)}
  {p q f0 g0 : Site 2}
-- given
  (hpq : p ≠ q)
  (hfg : (hypercubicLattice 2).Adj f0 g0)
  (hshared : sharedPrimalEdge f0 g0 = s(p, q)) :
-- imply
  whb_faceRegion (G ⊔ edge p q) = (whb_faceRegion G).deleteEdges {s(f0, g0)} := by
-- proof
  apply StatMech.Lattice.jfc_whb_sup_edge G hpq hfg hshared

/--
[jfc_whb_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFaithfulCount.lean)
-/
@[path]
private lemma jfc_whb_bot_eq :
-- imply
  whb_faceRegion (⊥ : SimpleGraph (Site 2)) = hypercubicLattice 2 := by
-- proof
  apply StatMech.Lattice.jfc_whb_bot

/--
[jfc_sharedPrimalEdge_endpoint_not_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFaithfulCount.lean)
-/
@[path]
private lemma jfc_sharedPrimalEdge_endpoint_not_box_eq
  {R : ℕ}
  {f g : Site 2}
  {v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj f g)
  (hf : (f 0).natAbs ≥ R + 2 ∨ (f 1).natAbs ≥ R + 2)
  (hv : v ∈ sharedPrimalEdge f g) :
-- imply
  v ∉ box 2 R := by
-- proof
  apply StatMech.Lattice.jfc_sharedPrimalEdge_endpoint_not_box R hadj hf hv

/--
[jfc_exterior_sharedEdge_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFaithfulCount.lean)
-/
@[path]
private lemma jfc_exterior_sharedEdge_not_mem_eq
  {H : SimpleGraph (Site 2)}
  {R : ℕ}
  {f g : Site 2}
-- given
  (hR : ∀ v ∈ H.support, v ∈ box 2 R)
  (hf : f ∈ exterior 2 (R + 1))
  (hadj : (hypercubicLattice 2).Adj f g) :
-- imply
  sharedPrimalEdge f g ∉ H.edgeSet := by
-- proof
  apply StatMech.Lattice.jfc_exterior_sharedEdge_not_mem H R hR hf hadj

/--
[jfc_whb_adj_of_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFaithfulCount.lean)
-/
@[path]
private lemma jfc_whb_adj_of_exterior_eq
  {H : SimpleGraph (Site 2)}
  {R : ℕ}
  {f g : Site 2}
-- given
  (hR : ∀ v ∈ H.support, v ∈ box 2 R)
  (hf : f ∈ exterior 2 (R + 1))
  (hadj : (hypercubicLattice 2).Adj f g) :
-- imply
  (whb_faceRegion H).Adj f g := by
-- proof
  apply StatMech.Lattice.jfc_whb_adj_of_exterior H R hR hf hadj

/--
[jfc_whb_regionComponents_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFaithfulCount.lean)
-/
@[path]
private lemma jfc_whb_regionComponents_finite_eq
  {H : SimpleGraph (Site 2)}
-- given
  (hfin : H.edgeSet.Finite) :
-- imply
  Empty.Finite (whb_faceRegion H).ConnectedComponent := by
-- proof
  apply StatMech.Lattice.jfc_whb_regionComponents_finite H hfin

/--
[jfc_whb_pushGraph_regionComponents_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFaithfulCount.lean)
-/
@[path]
private lemma jfc_whb_pushGraph_regionComponents_finite_eq
  {P : PlanarZ2Subgraph}
  {K : SimpleGraph P.V} :
-- imply
  Empty.Finite (whb_faceRegion (jei_pushGraph P K)).ConnectedComponent := by
-- proof
  apply StatMech.Lattice.jfc_whb_pushGraph_regionComponents_finite P K

/--
[jfc_flankingFaces](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFaithfulCount.lean)
-/
@[path]
private lemma jfc_flankingFaces_eq
  {p q : Site 2}
-- given
  (hpq : (hypercubicLattice 2).Adj p q) :
-- imply
  ∃ f0 g0 : Site 2, (hypercubicLattice 2).Adj f0 g0 ∧ sharedPrimalEdge f0 g0 = s(p, q) := by
-- proof
  apply StatMech.Lattice.jfc_flankingFaces hpq

/--
[jfc_flankingEdge_present](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFaithfulCount.lean)
-/
@[path]
private lemma jfc_flankingEdge_present_eq
  {P : PlanarZ2Subgraph}
  {K : SimpleGraph P.V}
  {x y : P.V}
  {f0 g0 : Site 2}
-- given
  (hadjG : P.G.Adj x y)
  (hnotK : ¬ K.Adj x y)
  (hfg : (hypercubicLattice 2).Adj f0 g0)
  (hshared : sharedPrimalEdge f0 g0 = s(P.emb x, P.emb y)) :
-- imply
  s(f0, g0) ∈ (whb_faceRegion (jei_pushGraph P K)).edgeSet := by
-- proof
  apply StatMech.Lattice.jfc_flankingEdge_present P K hadjG hnotK hfg hshared

/--
[jfc_whb_delete_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFaithfulCount.lean)
-/
@[path]
private lemma jfc_whb_delete_dichotomy_eq
  {G : SimpleGraph (Site 2)}
  {p q f0 g0 : Site 2}
  [Empty.Finite (whb_faceRegion G).ConnectedComponent]
  [Empty.Finite (whb_faceRegion (G ⊔ edge p q)).ConnectedComponent]
-- given
  (hpq : p ≠ q)
  (hfg : (hypercubicLattice 2).Adj f0 g0)
  (hshared : sharedPrimalEdge f0 g0 = s(p, q))
  (hpres : s(f0, g0) ∈ (whb_faceRegion G).edgeSet) :
-- imply
  (((whb_faceRegion G).deleteEdges {s(f0, g0)}).Reachable f0 g0 → Nat.card (whb_faceRegion (G ⊔ edge p q)).ConnectedComponent = Nat.card (whb_faceRegion G).ConnectedComponent) ∧ (¬ ((whb_faceRegion G).deleteEdges {s(f0, g0)}).Reachable f0 g0 → Nat.card (whb_faceRegion (G ⊔ edge p q)).ConnectedComponent = Nat.card (whb_faceRegion G).ConnectedComponent + 1) := by
-- proof
  apply StatMech.Lattice.jfc_whb_delete_dichotomy G hpq hfg hshared hpres

/--
[jfc_whb_count_of_sync](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFaithfulCount.lean)
-/
@[path]
private lemma jfc_whb_count_of_sync_eq
  {P : PlanarZ2Subgraph}
-- given
  (hsync : jfc_WhbSync P) :
-- imply
  ∀ (K : SimpleGraph P.V), K ≤ P.G → Nat.card (whb_faceRegion (jei_pushGraph P K)).ConnectedComponent = faceCount K := by
-- proof
  apply StatMech.Lattice.jfc_whb_count_of_sync P hsync

/--
[jfc_imageGraph_support_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFaithfulCount.lean)
-/
@[path]
private lemma jfc_imageGraph_support_box_eq
  {P : PlanarZ2Subgraph} :
-- imply
  ∀ v ∈ (imageGraph P).support, v ∈ box 2 (outerBoxRadius P) := by
-- proof
  apply StatMech.Lattice.jfc_imageGraph_support_box P

/--
[jfc_whb_exterior_in_outerRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFaithfulCount.lean)
-/
@[path]
private lemma jfc_whb_exterior_in_outerRegion_eq
  {P : PlanarZ2Subgraph}
  {x : Site 2}
-- given
  (hx : x ∈ exterior 2 (outerBoxRadius P + 1)) :
-- imply
  (whb_faceRegion (imageGraph P)).connectedComponentMk x = jfc_whb_outerRegion P := by
-- proof
  apply StatMech.Lattice.jfc_whb_exterior_in_outerRegion P hx

/--
[jfc_whb_outerRegion_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFaithfulCount.lean)
-/
@[path]
private lemma jfc_whb_outerRegion_infinite_eq
  {P : PlanarZ2Subgraph} :
-- imply
  (jfc_whb_outerRegion P).supp.Infinite := by
-- proof
  apply StatMech.Lattice.jfc_whb_outerRegion_infinite P

/--
[jfc_whb_infiniteComponent_meets_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFaithfulCount.lean)
-/
@[path]
private lemma jfc_whb_infiniteComponent_meets_exterior_eq
  {P : PlanarZ2Subgraph}
  {C : (whb_faceRegion (imageGraph P)).ConnectedComponent}
-- given
  (hC : C.supp.Infinite) :
-- imply
  ∃ x ∈ C.supp, x ∈ exterior 2 (outerBoxRadius P + 1) := by
-- proof
  apply StatMech.Lattice.jfc_whb_infiniteComponent_meets_exterior P hC

/--
[jfc_whb_unique_infinite_component](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFaithfulCount.lean)
-/
@[path]
private lemma jfc_whb_unique_infinite_component_eq
  {P : PlanarZ2Subgraph} :
-- imply
  ∃! C : (whb_faceRegion (imageGraph P)).ConnectedComponent, C.supp.Infinite := by
-- proof
  apply StatMech.Lattice.jfc_whb_unique_infinite_component P

/--
[jfc_whb_bounded_iff_ne_outer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFaithfulCount.lean)
-/
@[path]
private lemma jfc_whb_bounded_iff_ne_outer_eq
  {P : PlanarZ2Subgraph}
  {C : (whb_faceRegion (imageGraph P)).ConnectedComponent} :
-- imply
  C.supp.Finite ↔ C ≠ jfc_whb_outerRegion P := by
-- proof
  apply StatMech.Lattice.jfc_whb_bounded_iff_ne_outer P C

/--
[jfc_whb_bounded_add_one_eq_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFaithfulCount.lean)
-/
@[path]
private lemma jfc_whb_bounded_add_one_eq_card_eq
  {P : PlanarZ2Subgraph} :
-- imply
  whc_faithfulRegionCount P + 1 = Nat.card (whb_faceRegion (imageGraph P)).ConnectedComponent := by
-- proof
  apply StatMech.Lattice.jfc_whb_bounded_add_one_eq_card P

/--
[jfc_whb_total_count_of_sync](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFaithfulCount.lean)
-/
@[path]
private lemma jfc_whb_total_count_of_sync_eq
  {P : PlanarZ2Subgraph}
-- given
  (hsync : jfc_WhbSync P) :
-- imply
  Nat.card (whb_faceRegion (imageGraph P)).ConnectedComponent = faceCount P.G := by
-- proof
  apply StatMech.Lattice.jfc_whb_total_count_of_sync P hsync

/--
[jfc_whb_faithfulRegionCount_eq_nullity_of_sync](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFaithfulCount.lean)
-/
@[path]
private lemma jfc_whb_faithfulRegionCount_eq_nullity_of_sync_eq
  {P : PlanarZ2Subgraph}
-- given
  (hsync : jfc_WhbSync P) :
-- imply
  whc_faithfulRegionCount P = nullity P.G := by
-- proof
  apply StatMech.Lattice.jfc_whb_faithfulRegionCount_eq_nullity_of_sync P hsync

/--
[jfc_faithfulDiscreteJordan_of_sync](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFaithfulCount.lean)
-/
@[path]
private lemma jfc_faithfulDiscreteJordan_of_sync_eq
  {P : PlanarZ2Subgraph}
-- given
  (hsync : jfc_WhbSync P) :
-- imply
  whc_FaithfulDiscreteJordan P := by
-- proof
  apply StatMech.Lattice.jfc_faithfulDiscreteJordan_of_sync P hsync

/--
[jfc_pushGraph_le_lattice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFaithfulCount.lean)
-/
@[path]
private lemma jfc_pushGraph_le_lattice_eq
  {P : PlanarZ2Subgraph}
  {K : SimpleGraph P.V}
-- given
  (hKle : K ≤ P.G) :
-- imply
  jei_pushGraph P K ≤ hypercubicLattice 2 := by
-- proof
  apply StatMech.Lattice.jfc_pushGraph_le_lattice P K hKle

/--
[jfc_whbSync_step_of_evenContour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFaithfulCount.lean)
-/
@[path]
private lemma jfc_whbSync_step_of_evenContour_eq
  {P : PlanarZ2Subgraph}
  {K : SimpleGraph P.V}
  {x y : P.V}
  {f0 g0 : Site 2}
-- given
  (hKle : K ≤ P.G)
  (hadjG : P.G.Adj x y)
  (hnotK : ¬ K.Adj x y)
  (hfg : (hypercubicLattice 2).Adj f0 g0)
  (hshared : sharedPrimalEdge f0 g0 = s(P.emb x, P.emb y))
  (hcc : jce_ClosedContour ((insert (sharedPrimalEdge f0 g0) (jei_pushGraph_edgeSet_finite P K).toFinset : Finset (Sym2 (Site 2))) : Set (Sym2 (Site 2)))) :
-- imply
  (K.Reachable x y ↔ ¬ ((whb_faceRegion (jei_pushGraph P K)).deleteEdges {s(f0, g0)}).Reachable f0 g0) := by
-- proof
  apply StatMech.Lattice.jfc_whbSync_step_of_evenContour P K hKle hadjG hnotK hfg hshared hcc

/--
[jfc_faithfulCountResidue_of_threading](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFaithfulCount.lean)
-/
@[path]
private lemma jfc_faithfulCountResidue_of_threading_eq
-- given
  (hthr : jfc_EvenDegreeThreading) :
-- imply
  jeb_FaithfulCountResidue := by
-- proof
  apply StatMech.Lattice.jfc_faithfulCountResidue_of_threading hthr

/--
[jfc_evenDegreeThreading_of_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFaithfulCount.lean)
-/
@[path]
private lemma jfc_evenDegreeThreading_of_bot_eq
  {P : PlanarZ2Subgraph}
-- given
  (hG : P.G = ⊥) :
-- imply
  jfc_WhbSync P := by
-- proof
  apply StatMech.Lattice.jfc_evenDegreeThreading_of_bot hG

/--
[jfc_latadj_E](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFaithfulCount.lean)
-/
@[path]
private lemma jfc_latadj_E_eq
  {a b : ℤ} :
-- imply
  (hypercubicLattice 2).Adj ![a, b] ![a + 1, b] := by
-- proof
  apply StatMech.Lattice.jfc_latadj_E a b

/--
[jfc_latadj_N](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFaithfulCount.lean)
-/
@[path]
private lemma jfc_latadj_N_eq
  {a b : ℤ} :
-- imply
  (hypercubicLattice 2).Adj ![a, b] ![a, b + 1] := by
-- proof
  apply StatMech.Lattice.jfc_latadj_N a b

/--
[jfc_sq_adj_of_ne_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFaithfulCount.lean)
-/
@[path]
private lemma jfc_sq_adj_of_ne_origin_eq
  {f g : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj f g)
  (hf : f ≠ ![0, 0])
  (hg : g ≠ ![0, 0]) :
-- imply
  (whb_faceRegion (imageGraph jbc_Pce)).Adj f g := by
-- proof
  apply StatMech.Lattice.jfc_sq_adj_of_ne_origin hadj hf hg

/--
[jfc_sq_row_east](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFaithfulCount.lean)
-/
@[path]
private lemma jfc_sq_row_east_eq
  {b : ℤ}
  {a : ℤ}
  {n : ℕ}
-- given
  (hb : b ≠ 0) :
-- imply
  (whb_faceRegion (imageGraph jbc_Pce)).Reachable ![a, b] ![a + n, b] := by
-- proof
  apply StatMech.Lattice.jfc_sq_row_east b hb a n

/--
[jfc_sq_col_north](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFaithfulCount.lean)
-/
@[path]
private lemma jfc_sq_col_north_eq
  {a : ℤ}
  {b : ℤ}
  {n : ℕ}
-- given
  (ha : a ≠ 0) :
-- imply
  (whb_faceRegion (imageGraph jbc_Pce)).Reachable ![a, b] ![a, b + n] := by
-- proof
  apply StatMech.Lattice.jfc_sq_col_north a ha b n

/--
[jfc_sq_farEast_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFaithfulCount.lean)
-/
@[path]
private lemma jfc_sq_farEast_exterior_eq
  {M : ℕ}
  {a b : ℤ} :
-- imply
  (![a + ((M + 1 + a.natAbs : ℕ) : ℤ), b] : Site 2) ∈ exterior 2 M := by
-- proof
  apply StatMech.Lattice.jfc_sq_farEast_exterior M a b

/--
[jfc_sq_reach_outerRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFaithfulCount.lean)
-/
@[path]
private lemma jfc_sq_reach_outerRegion_eq
  {v : Site 2}
-- given
  (hv : v ≠ ![0, 0]) :
-- imply
  (whb_faceRegion (imageGraph jbc_Pce)).connectedComponentMk v = jfc_whb_outerRegion jbc_Pce := by
-- proof
  apply StatMech.Lattice.jfc_sq_reach_outerRegion hv

/--
[jfc_sq_interior_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFaithfulCount.lean)
-/
@[path]
private lemma jfc_sq_interior_bounded_eq :
-- imply
  jfc_sq_interior.supp.Finite := by
-- proof
  apply StatMech.Lattice.jfc_sq_interior_bounded

/--
[jfc_sq_bounded_eq_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFaithfulCount.lean)
-/
@[path]
private lemma jfc_sq_bounded_eq_interior_eq
  {C : {c : (whb_faceRegion (imageGraph jbc_Pce)).ConnectedComponent // c.supp.Finite}} :
-- imply
  C = ⟨jfc_sq_interior, jfc_sq_interior_bounded⟩ := by
-- proof
  apply StatMech.Lattice.jfc_sq_bounded_eq_interior C

/--
[jfc_sq_faithfulRegionCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFaithfulCount.lean)
-/
@[path]
private lemma jfc_sq_faithfulRegionCount_eq :
-- imply
  whc_faithfulRegionCount jbc_Pce = 1 := by
-- proof
  apply StatMech.Lattice.jfc_sq_faithfulRegionCount

/--
[jfc_sq_nullity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFaithfulCount.lean)
-/
@[path]
private lemma jfc_sq_nullity_eq :
-- imply
  nullity jbc_Pce.G = 1 := by
-- proof
  apply StatMech.Lattice.jfc_sq_nullity

/--
[jfc_faithfulDiscreteJordan_unitSquare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFaithfulCount.lean)
-/
@[path]
private lemma jfc_faithfulDiscreteJordan_unitSquare_eq :
-- imply
  whc_FaithfulDiscreteJordan jbc_Pce := by
-- proof
  apply StatMech.Lattice.jfc_faithfulDiscreteJordan_unitSquare

/--
[jfc_summary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFaithfulCount.lean)
-/
@[path]
private lemma jfc_summary_eq :
-- imply
  whc_FaithfulDiscreteJordan jbc_Pce ∧ (jfc_EvenDegreeThreading → jeb_FaithfulCountResidue) := by
-- proof
  apply StatMech.Lattice.jfc_summary


-- created on 2026-10-23
