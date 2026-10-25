import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
open SimpleGraph Filter Topology Set MeasureTheory StatMech StatMech.FK StatMech.FK.EdgeCount


/--
[qp_fkZ_comap_range](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean)
-/
@[path]
private lemma qp_fkZ_comap_range_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {f : V → U}
  {g : W → U}
  {p q : ℝ}
  [DecidableRel (K₀.comap f).Adj]
  [DecidableRel (K₀.comap g).Adj]
-- given
  (hf : Function.Injective f)
  (hg : Function.Injective g)
  (hr : Set.range f = Set.range g) :
-- imply
  fkZ (K₀.comap f) p q = fkZ (K₀.comap g) p q := by
-- proof
  apply StatMech.FK.qp_fkZ_comap_range K₀ f g hf hg hr p q

/--
[qp_comap_comap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean)
-/
@[path]
private lemma qp_comap_comap_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  {g : W → U}
  {f : V → W} :
-- imply
  (K₀.comap g).comap f = K₀.comap (g ∘ f) := by
-- proof
  apply StatMech.FK.qp_comap_comap K₀ g f

/--
[qp_fkZ_ge_allClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean)
-/
@[path]
private lemma qp_fkZ_ge_allClosed_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq1 : 1 ≤ q) :
-- imply
  (1 - p) ^ G.edgeFinset.card ≤ fkZ G p q := by
-- proof
  apply StatMech.FK.qp_fkZ_ge_allClosed K₀ G hp hp1 hq1

/--
[qp_neglogZ_le_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean)
-/
@[path]
private lemma qp_neglogZ_le_edges_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq1 : 1 ≤ q) :
-- imply
  -Real.log (fkZ G p q) ≤ (G.edgeFinset.card : ℝ) * (-Real.log (1 - p)) := by
-- proof
  apply StatMech.FK.qp_neglogZ_le_edges K₀ G hp hp1 hq1

/--
[qp_fkZ_comapComap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean)
-/
@[path]
private lemma qp_fkZ_comapComap_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  [DecidableEq T]
  {tag : U → T}
  [Fintype V]
  [Fintype X]
  [DecidableEq V]
  [DecidableEq X]
  {g : W → U}
  {f : V → W}
  {p q : ℝ}
  [DecidableRel ((K₀.comap g).comap f).Adj]
  [DecidableRel (K₀.comap h).Adj]
-- given
  (h : X → U)
  (hgf : Function.Injective (g ∘ f))
  (hh : Function.Injective h)
  (hr : Set.range (g ∘ f) = Set.range h) :
-- imply
  fkZ ((K₀.comap g).comap f) p q = fkZ (K₀.comap h) p q := by
-- proof
  apply StatMech.FK.qp_fkZ_comapComap K₀ tag g f h hgf hh hr p q

/--
[qp_left_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean)
-/
@[path]
private lemma qp_left_eq_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  [DecidableEq T]
  {tag : U → T}
  {τ : T}
  {S : Finset T}
  {p q : ℝ}
-- given
  (hτ : τ ∉ S) :
-- imply
  fkZ (agl_left (qp_restG K₀ tag (insert τ S)) (fun x => tag x.1 = τ)) p q = fkZ (qp_blkG K₀ tag τ) p q := by
-- proof
  apply StatMech.FK.qp_left_eq K₀ tag τ S hτ p q

/--
[qp_right_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean)
-/
@[path]
private lemma qp_right_eq_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  [DecidableEq T]
  {tag : U → T}
  {τ : T}
  {S : Finset T}
  {p q : ℝ}
-- given
  (hτ : τ ∉ S) :
-- imply
  fkZ (agl_right (qp_restG K₀ tag (insert τ S)) (fun x => tag x.1 = τ)) p q = fkZ (qp_restG K₀ tag S) p q := by
-- proof
  apply StatMech.FK.qp_right_eq K₀ tag τ S hτ p q

/--
[qp_interface_le_straddle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean)
-/
@[path]
private lemma qp_interface_le_straddle_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  [DecidableEq T]
  {tag : U → T}
  [DecidablePred P]
-- given
  (P : U → Prop) :
-- imply
  agl_interfaceCard K₀ P ≤ (qp_straddleEdges K₀ P).card := by
-- proof
  apply StatMech.FK.qp_interface_le_straddle K₀ tag P

/--
[qp_restG_straddle_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean)
-/
@[path]
private lemma qp_restG_straddle_le_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  [DecidableEq T]
  {tag : U → T}
  {τ : T}
  {S : Finset T} :
-- imply
  (qp_straddleEdges (qp_restG K₀ tag (insert τ S)) (fun x => tag x.1 = τ)).card ≤ (qp_straddleEdges K₀ (fun u => tag u = τ)).card := by
-- proof
  apply StatMech.FK.qp_restG_straddle_le K₀ tag τ S

/--
[qp_fkZ_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean)
-/
@[path]
private lemma qp_fkZ_empty_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  [DecidableEq T]
  {tag : U → T}
  [Fintype V]
  [DecidableEq V]
  [IsEmpty V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ} :
-- imply
  fkZ G p q = 1 := by
-- proof
  apply StatMech.FK.qp_fkZ_empty K₀ tag G p q

/--
[qp_peel_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean)
-/
@[path]
private lemma qp_peel_le_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  [DecidableEq T]
  {tag : U → T}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  ∀ S : Finset T, ∃ I : ℕ, qp_uu (qp_restG K₀ tag S) p q ≤ (∑ τ ∈ S, qp_uu (qp_blkG K₀ tag τ) p q) + (I : ℝ) * (-Real.log (1 - p)) ∧ I ≤ ∑ τ ∈ S, (qp_straddleEdges K₀ (fun u => tag u = τ)).card := by
-- proof
  apply StatMech.FK.qp_peel_le K₀ tag p q hp hp1 hq

/--
[shift_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean)
-/
@[path]
private lemma shift_adj_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  {d n : ℕ}
  {i : Fin d}
  {x : Site d}
  {b : ℤ}
-- given
  (hb : b = 1 ∨ b = -1) :
-- imply
  (hypercubicLattice d).Adj x (Function.update x i (x i + b)) := by
-- proof
  apply StatMech.FK.EdgeCount.shift_adj K₀ d n i x b hb

/--
[card_shiftDom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean)
-/
@[path]
private lemma card_shiftDom_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  {d n : ℕ}
  {i : Fin d}
  {b : ℤ}
-- given
  (hb : b = 1 ∨ b = -1)
  (hd : 1 ≤ d) :
-- imply
  (shiftDom d n i b).card = (2 * n) * (2 * n + 1) ^ (d - 1) := by
-- proof
  apply StatMech.FK.EdgeCount.card_shiftDom K₀ d n i b hb hd

/--
[shiftMap_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean)
-/
@[path]
private lemma shiftMap_mem_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  {d n : ℕ}
  {i : Fin d}
  {b : ℤ}
  {x : Site d}
-- given
  (hb : b = 1 ∨ b = -1)
  (hx : x ∈ shiftDom d n i b) :
-- imply
  shiftMap d n i b x ∈ edgeAxisI d n i := by
-- proof
  apply StatMech.FK.EdgeCount.shiftMap_mem K₀ d n i b hb x hx

/--
[shiftMap_inj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean)
-/
@[path]
private lemma shiftMap_inj_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  {d n : ℕ}
  {i : Fin d}
  {b : ℤ} :
-- imply
  Function.Injective (shiftMap d n i b) := by
-- proof
  apply StatMech.FK.EdgeCount.shiftMap_inj K₀ d n i b

/--
[edgeAxisI_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean)
-/
@[path]
private lemma edgeAxisI_eq_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  {d n : ℕ}
  {i : Fin d} :
-- imply
  edgeAxisI d n i = (shiftDom d n i 1).image (shiftMap d n i 1) ∪ (shiftDom d n i (-1)).image (shiftMap d n i (-1)) := by
-- proof
  apply StatMech.FK.EdgeCount.edgeAxisI_eq K₀ d n i

/--
[fwd_bwd_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean)
-/
@[path]
private lemma fwd_bwd_disjoint_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  {d n : ℕ}
  {i : Fin d} :
-- imply
  Disjoint ((shiftDom d n i 1).image (shiftMap d n i 1)) ((shiftDom d n i (-1)).image (shiftMap d n i (-1))) := by
-- proof
  apply StatMech.FK.EdgeCount.fwd_bwd_disjoint K₀ d n i

/--
[card_edgeAxisI](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean)
-/
@[path]
private lemma card_edgeAxisI_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  {d n : ℕ}
  {i : Fin d}
-- given
  (hd : 1 ≤ d) :
-- imply
  (edgeAxisI d n i).card = 2 * ((2 * n) * (2 * n + 1) ^ (d - 1)) := by
-- proof
  apply StatMech.FK.EdgeCount.card_edgeAxisI K₀ d n i hd

/--
[edgeF_biUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean)
-/
@[path]
private lemma edgeF_biUnion_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  {d n : ℕ} :
-- imply
  (boxSV_edgeF d n) = Finset.univ.biUnion (fun i : Fin d => edgeAxisI d n i) := by
-- proof
  apply StatMech.FK.EdgeCount.edgeF_biUnion K₀ d n

/--
[edgeAxis_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean)
-/
@[path]
private lemma edgeAxis_disjoint_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  {d n : ℕ}
  {i j : Fin d}
-- given
  (hij : i ≠ j) :
-- imply
  Disjoint (edgeAxisI d n i) (edgeAxisI d n j) := by
-- proof
  apply StatMech.FK.EdgeCount.edgeAxis_disjoint K₀ d n i j hij

/--
[edgeCard_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean)
-/
@[path]
private lemma edgeCard_eq_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  {d n : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  boxSV_edgeCard d n = d * (2 * ((2 * n) * (2 * n + 1) ^ (d - 1))) := by
-- proof
  apply StatMech.FK.EdgeCount.edgeCard_eq K₀ d n hd

/--
[boxGraph_edgeCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean)
-/
@[path]
private lemma boxGraph_edgeCard_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  {d n : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  (boxGraph d n).edgeFinset.card = d * ((2 * n) * (2 * n + 1) ^ (d - 1)) := by
-- proof
  apply StatMech.FK.EdgeCount.boxGraph_edgeCard K₀ d n hd

/--
[qp_natAbs_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean)
-/
@[path]
private lemma qp_natAbs_iff_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  {x : ℤ}
  {n : ℕ} :
-- imply
  x.natAbs ≤ n ↔ -(n : ℤ) ≤ x ∧ x ≤ n := by
-- proof
  apply StatMech.FK.qp_natAbs_iff K₀ x n

/--
[qp_boxTag_some_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean)
-/
@[path]
private lemma qp_boxTag_some_iff_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  {d K : ℕ}
  {x : boxVerts d (2 * K + 1)}
  {s : Fin d → Bool} :
-- imply
  qp_boxTag d K x = some s ↔ ∀ i, if s i then (1 ≤ (x : Site d) i ∧ (x : Site d) i ≤ 2 * K + 1) else (-(2 * K + 1 : ℤ) ≤ (x : Site d) i ∧ (x : Site d) i ≤ -1) := by
-- proof
  apply StatMech.FK.qp_boxTag_some_iff K₀ d K x s

/--
[qp_block_fkZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean)
-/
@[path]
private lemma qp_block_fkZ_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  {d K : ℕ}
  {s : Fin d → Bool}
  {p q : ℝ} :
-- imply
  fkZ (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) (some s)) p q = fkZ (boxGraph d K) p q := by
-- proof
  apply StatMech.FK.qp_block_fkZ K₀ d K s p q

/--
[qp_Jset_subset_biUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean)
-/
@[path]
private lemma qp_Jset_subset_biUnion_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  {d K : ℕ} :
-- imply
  qp_Jset d K ⊆ Finset.univ.biUnion (fun i : Fin d => qp_Jslab d K i) := by
-- proof
  apply StatMech.FK.qp_Jset_subset_biUnion K₀ d K

/--
[qp_Jslab_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean)
-/
@[path]
private lemma qp_Jslab_card_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  {d K : ℕ}
  {i : Fin d}
-- given
  (hd : 1 ≤ d) :
-- imply
  (qp_Jslab d K i).card ≤ (2 * (2 * K + 1) + 1) ^ (d - 1) := by
-- proof
  apply StatMech.FK.qp_Jslab_card K₀ d K hd i

/--
[qp_Jset_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean)
-/
@[path]
private lemma qp_Jset_card_le_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  {d K : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  (qp_Jset d K).card ≤ d * (2 * (2 * K + 1) + 1) ^ (d - 1) := by
-- proof
  apply StatMech.FK.qp_Jset_card_le K₀ d K hd

/--
[qp_boxGraph_degree_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean)
-/
@[path]
private lemma qp_boxGraph_degree_le_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  {d n : ℕ}
  {v : boxVerts d n} :
-- imply
  (boxGraph d n).degree v ≤ 2 * d := by
-- proof
  apply StatMech.FK.qp_boxGraph_degree_le K₀ d n v

/--
[qp_straddle_endpoint_in_J](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean)
-/
@[path]
private lemma qp_straddle_endpoint_in_J_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  {d K : ℕ}
  {s : Fin d → Bool}
  {x y : boxVerts d (2 * K + 1)}
-- given
  (hadj : (boxGraph d (2 * K + 1)).Adj x y)
  (hx : qp_boxTag d K x = some s)
  (hy : qp_boxTag d K y ≠ some s) :
-- imply
  ∃ i, (y : Site d) i = 0 := by
-- proof
  apply StatMech.FK.qp_straddle_endpoint_in_J K₀ d K s x y hadj hx hy

/--
[qp_tag_none_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean)
-/
@[path]
private lemma qp_tag_none_iff_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  {d K : ℕ}
  {x : boxVerts d (2 * K + 1)} :
-- imply
  qp_boxTag d K x = none ↔ ∃ i, (x : Site d) i = 0 := by
-- proof
  apply StatMech.FK.qp_tag_none_iff K₀ d K x

/--
[qp_straddle_endpoint_in_J_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean)
-/
@[path]
private lemma qp_straddle_endpoint_in_J_all_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  {d K : ℕ}
  {τ : Option (Fin d → Bool)}
  {x y : boxVerts d (2 * K + 1)}
-- given
  (hadj : (boxGraph d (2 * K + 1)).Adj x y)
  (hx : qp_boxTag d K x = τ)
  (hy : qp_boxTag d K y ≠ τ) :
-- imply
  (∃ i, (x : Site d) i = 0) ∨ (∃ i, (y : Site d) i = 0) := by
-- proof
  apply StatMech.FK.qp_straddle_endpoint_in_J_all K₀ d K τ x y hadj hx hy

/--
[qp_straddle_subset_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean)
-/
@[path]
private lemma qp_straddle_subset_all_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  {d K : ℕ}
  {τ : Option (Fin d → Bool)} :
-- imply
  qp_straddleEdges (boxGraph d (2 * K + 1)) (fun x => qp_boxTag d K x = τ) ⊆ (qp_Jset d K).biUnion (fun v => (boxGraph d (2 * K + 1)).incidenceFinset v) := by
-- proof
  apply StatMech.FK.qp_straddle_subset_all K₀ d K τ

/--
[qp_straddle_card_le_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean)
-/
@[path]
private lemma qp_straddle_card_le_all_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  {d K : ℕ}
  {τ : Option (Fin d → Bool)} :
-- imply
  (qp_straddleEdges (boxGraph d (2 * K + 1)) (fun x => qp_boxTag d K x = τ)).card ≤ 2 * d * (qp_Jset d K).card := by
-- proof
  apply StatMech.FK.qp_straddle_card_le_all K₀ d K τ

/--
[qp_blkNone_edge_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean)
-/
@[path]
private lemma qp_blkNone_edge_le_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  {d K : ℕ} :
-- imply
  (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) none).edgeFinset.card ≤ 2 * d * (qp_Jset d K).card := by
-- proof
  apply StatMech.FK.qp_blkNone_edge_le K₀ d K

/--
[qp_restG_univ_fkZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean)
-/
@[path]
private lemma qp_restG_univ_fkZ_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  {d K : ℕ}
  {p q : ℝ} :
-- imply
  fkZ (qp_restG (boxGraph d (2 * K + 1)) (qp_boxTag d K) Finset.univ) p q = fkZ (boxGraph d (2 * K + 1)) p q := by
-- proof
  apply StatMech.FK.qp_restG_univ_fkZ K₀ d K p q

/--
[qp_box_neglog_doubling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean)
-/
@[path]
private lemma qp_box_neglog_doubling_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  {d K : ℕ}
  {t : ℝ} :
-- imply
  agl_u d t (2 * K + 1) ≤ (2 : ℝ) ^ d * agl_u d t K + ((2 * d * (qp_Jset d K).card + (2 ^ d + 1) * (2 * d * (qp_Jset d K).card) : ℕ) : ℝ) * (-Real.log (1 - fsc_logistic t)) := by
-- proof
  apply StatMech.FK.qp_box_neglog_doubling K₀ d K t

/--
[qp_edge_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean)
-/
@[path]
private lemma qp_edge_le_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  {d K : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  (2 : ℝ) ^ d * ((boxGraph d K).edgeFinset.card) ≤ ((boxGraph d (2 * K + 1)).edgeFinset.card) := by
-- proof
  apply StatMech.FK.qp_edge_le K₀ d K hd

/--
[qp_edge_gap_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean)
-/
@[path]
private lemma qp_edge_gap_le_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  {d K : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  (((boxGraph d (2 * K + 1)).edgeFinset.card : ℝ)) - (2 : ℝ) ^ d * ((boxGraph d K).edgeFinset.card) ≤ (d : ℝ) * (d + 2) * (4 * K + 3) ^ (d - 1) := by
-- proof
  apply StatMech.FK.qp_edge_gap_le K₀ d K hd

/--
[qp_edge_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean)
-/
@[path]
private lemma qp_edge_lower_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  {d n : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  (n : ℝ) * (2 * (n : ℝ) + 1) ^ (d - 1) ≤ ((boxGraph d n).edgeFinset.card : ℝ) := by
-- proof
  apply StatMech.FK.qp_edge_lower K₀ d n hd

/--
[qp_summable_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean)
-/
@[path]
private lemma qp_summable_ratio_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  {d : ℕ}
  {I : ℕ → ℝ}
-- given
  (hd : 1 ≤ d)
  (hIbd : ∀ j, I j ≤ ((2 ^ d + 2) * (2 * d * d) + d * (d + 2) : ℝ) * (4 * (agl_K j : ℝ) + 3) ^ (d - 1))
  (hI0 : ∀ j, 0 ≤ I j) :
-- imply
  Summable (fun j => I j / agl_E d (agl_K (j + 1))) := by
-- proof
  apply StatMech.FK.qp_summable_ratio K₀ d hd I hIbd hI0

/--
[qp_additiveDoublingBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean)
-/
@[path]
private lemma qp_additiveDoublingBound_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  {d : ℕ}
  {t : ℝ}
-- given
  (hd : 1 ≤ d) :
-- imply
  agl_AdditiveDoublingBound d t := by
-- proof
  apply StatMech.FK.qp_additiveDoublingBound K₀ d hd t

/--
[qp_additiveBoxFeketeData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean)
-/
@[path]
private lemma qp_additiveBoxFeketeData_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  {d : ℕ}
  {t : ℝ}
-- given
  (hd : 1 ≤ d)
  (hbdd : ∃ M : ℝ, ∀ j, |agl_u d t (agl_K j) / agl_E d (agl_K j)| ≤ M)
  (hosc : ∃ (bj : ℕ → ℕ) (osc : ℕ → ℝ), Tendsto bj atTop atTop ∧ Tendsto osc atTop (𝓝 0) ∧ (∀ n, |ivp2_tiltFreeEnergy (boxGraph d n) 2 t - ivp2_tiltFreeEnergy (boxGraph d (agl_K (bj n))) 2 t| ≤ osc (bj n))) :
-- imply
  agl_AdditiveBoxFeketeData d t := by
-- proof
  apply StatMech.FK.qp_additiveBoxFeketeData K₀ d hd t hbdd hosc

/--
[qp_fk_uniqueness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean)
-/
@[path]
private lemma qp_fk_uniqueness_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  {d : ℕ}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
-- given
  (hd : 1 ≤ d)
  (heb : eb ∈ (boxGraph d N).edgeFinset)
  (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hbdd : ∀ t, ∃ M : ℝ, ∀ j, |agl_u d t (agl_K j) / agl_E d (agl_K j)| ≤ M)
  (hosc : ∀ t, ∃ (bj : ℕ → ℕ) (osc : ℕ → ℝ), Tendsto bj atTop atTop ∧ Tendsto osc atTop (𝓝 0) ∧ (∀ n, |ivp2_tiltFreeEnergy (boxGraph d n) 2 t - ivp2_tiltFreeEnergy (boxGraph d (agl_K (bj n))) 2 t| ≤ osc (bj n))) :
-- imply
  {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧ eventMassProb (fuc_freeMass d N t) A ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable := by
-- proof
  apply StatMech.FK.qp_fk_uniqueness K₀ d hd N eb heb hEbox hbdd hosc


-- created on 2026-10-23
