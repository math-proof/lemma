import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.EdgeConfigZ.Part15
open SimpleGraph Filter Topology Set StatMech StatMech.FK


/--
[ecz_openSub_eq_of_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_openSub_eq_of_edges_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {ω₁ ω₂ : ConfigSpace (Sym2 V)}
-- given
  (h : ∀ e ∈ G.edgeFinset, ω₁ e = ω₂ e) :
-- imply
  openSub G ω₁ = openSub G ω₂ := by
-- proof
  apply StatMech.FK.ecz_openSub_eq_of_edges G ω₁ ω₂ h

/--
[ecz_numClusters_eq_of_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_numClusters_eq_of_edges_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {ω₁ ω₂ : ConfigSpace (Sym2 V)}
-- given
  (h : ∀ e ∈ G.edgeFinset, ω₁ e = ω₂ e) :
-- imply
  numClusters G ω₁ = numClusters G ω₂ := by
-- proof
  apply StatMech.FK.ecz_numClusters_eq_of_edges G ω₁ ω₂ h

/--
[ecz_fkWeight_eq_of_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_fkWeight_eq_of_edges_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {ω₁ ω₂ : ConfigSpace (Sym2 V)}
-- given
  (h : ∀ e ∈ G.edgeFinset, ω₁ e = ω₂ e) :
-- imply
  fkWeight G p q ω₁ = fkWeight G p q ω₂ := by
-- proof
  apply StatMech.FK.ecz_fkWeight_eq_of_edges G p q ω₁ ω₂ h

/--
[ecz_NE_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_NE_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  ecz_NE G = Fintype.card (Sym2 V) - G.edgeFinset.card := by
-- proof
  apply StatMech.FK.ecz_NE_eq G

/--
[ecz_fkZEdge_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_fkZEdge_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 < ecz_fkZEdge G p q := by
-- proof
  apply StatMech.FK.ecz_fkZEdge_pos G hp hp1 hq

/--
[ecz_fkZEdge_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_fkZEdge_ne_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  ecz_fkZEdge G p q ≠ 0 := by
-- proof
  apply StatMech.FK.ecz_fkZEdge_ne_zero G hp hp1 hq

/--
[ecz_factorization](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_factorization_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ} :
-- imply
  fkZ G p q = 2 ^ ecz_NE G * ecz_fkZEdge G p q := by
-- proof
  apply StatMech.FK.ecz_factorization G p q

/--
[ecz_fkZEdge_eq_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_fkZEdge_eq_div_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ} :
-- imply
  ecz_fkZEdge G p q = fkZ G p q / 2 ^ ecz_NE G := by
-- proof
  apply StatMech.FK.ecz_fkZEdge_eq_div G p q

/--
[ecz_NE_iso](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_NE_iso_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {φ : G ≃g H} :
-- imply
  ecz_NE G = ecz_NE H := by
-- proof
  apply StatMech.FK.ecz_NE_iso φ

/--
[ecz_fkZEdge_iso](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_fkZEdge_iso_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {φ : G ≃g H}
  {p q : ℝ} :
-- imply
  ecz_fkZEdge G p q = ecz_fkZEdge H p q := by
-- proof
  apply StatMech.FK.ecz_fkZEdge_iso φ p q

/--
[ecz_combine_closedOff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_combine_closedOff_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {σ : ecz_ClosedOff G}
  {τ : ecz_ClosedOff H}
  {e : Sym2 (V ⊕ W)}
-- given
  (hci : fis_CrossInterface G H K)
  (he : e ∉ K.edgeFinset) :
-- imply
  fsm_combine σ.val τ.val e = false := by
-- proof
  apply StatMech.FK.ecz_combine_closedOff hci σ τ e he

/--
[ecz_fkZEdge_interface_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_fkZEdge_interface_ge_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {p q : ℝ}
-- given
  (hci : fis_CrossInterface G H K)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (1 - p) ^ (fis_interface G H K).card * (ecz_fkZEdge G p q * ecz_fkZEdge H p q) ≤ ecz_fkZEdge K p q := by
-- proof
  apply StatMech.FK.ecz_fkZEdge_interface_ge hci hp hp1 hq

/--
[ecz_neglog_interface_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_neglog_interface_le_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {p q : ℝ}
-- given
  (hci : fis_CrossInterface G H K)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  - Real.log (ecz_fkZEdge K p q) ≤ - Real.log (ecz_fkZEdge G p q) + - Real.log (ecz_fkZEdge H p q) - (fis_interface G H K).card * Real.log (1 - p) := by
-- proof
  apply StatMech.FK.ecz_neglog_interface_le hci hp hp1 hq

/--
[ecz_fkZEdge_ge_allClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_fkZEdge_ge_allClosed_eq
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
  (1 - p) ^ G.edgeFinset.card ≤ ecz_fkZEdge G p q := by
-- proof
  apply StatMech.FK.ecz_fkZEdge_ge_allClosed G hp hp1 hq1

/--
[ecz_neglogZEdge_le_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_neglogZEdge_le_edges_eq
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
  -Real.log (ecz_fkZEdge G p q) ≤ (G.edgeFinset.card : ℝ) * (-Real.log (1 - p)) := by
-- proof
  apply StatMech.FK.ecz_neglogZEdge_le_edges G hp hp1 hq1

/--
[ecz_neglog_partition_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_neglog_partition_le_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  [DecidablePred P]
  {p q : ℝ}
-- given
  (P : U → Prop)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  -Real.log (ecz_fkZEdge K₀ p q) ≤ -Real.log (ecz_fkZEdge (agl_left K₀ P) p q) + -Real.log (ecz_fkZEdge (agl_right K₀ P) p q) - (agl_interfaceCard K₀ P : ℝ) * Real.log (1 - p) := by
-- proof
  apply StatMech.FK.ecz_neglog_partition_le K₀ P hp hp1 hq

/--
[ecz_left_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_left_eq_eq
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
  ecz_fkZEdge (agl_left (qp_restG K₀ tag (insert τ S)) (fun x => tag x.1 = τ)) p q = ecz_fkZEdge (qp_blkG K₀ tag τ) p q := by
-- proof
  apply StatMech.FK.ecz_left_eq K₀ tag τ S hτ p q

/--
[ecz_right_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_right_eq_eq
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
  ecz_fkZEdge (agl_right (qp_restG K₀ tag (insert τ S)) (fun x => tag x.1 = τ)) p q = ecz_fkZEdge (qp_restG K₀ tag S) p q := by
-- proof
  apply StatMech.FK.ecz_right_eq K₀ tag τ S hτ p q

/--
[ecz_left_edge_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_left_edge_card_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  [DecidableEq T]
  {tag : U → T}
  {τ : T}
  {S : Finset T}
-- given
  (hτ : τ ∉ S) :
-- imply
  (agl_left (qp_restG K₀ tag (insert τ S)) (fun x => tag x.1 = τ)).edgeFinset.card = (qp_blkG K₀ tag τ).edgeFinset.card := by
-- proof
  apply StatMech.FK.ecz_left_edge_card K₀ tag τ S hτ

/--
[ecz_right_edge_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_right_edge_card_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  [DecidableEq T]
  {tag : U → T}
  {τ : T}
  {S : Finset T}
-- given
  (hτ : τ ∉ S) :
-- imply
  (agl_right (qp_restG K₀ tag (insert τ S)) (fun x => tag x.1 = τ)).edgeFinset.card = (qp_restG K₀ tag S).edgeFinset.card := by
-- proof
  apply StatMech.FK.ecz_right_edge_card K₀ tag τ S hτ

/--
[ecz_fkZEdge_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_fkZEdge_empty_eq
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
  ecz_fkZEdge G p q = 1 := by
-- proof
  apply StatMech.FK.ecz_fkZEdge_empty K₀ tag G p q

/--
[ecz_peel_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_peel_le_eq
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
  ∀ S : Finset T, ∃ I : ℕ, ecz_uu (qp_restG K₀ tag S) p q ≤ (∑ τ ∈ S, ecz_uu (qp_blkG K₀ tag τ) p q) + (I : ℝ) * (-Real.log (1 - p)) ∧ I ≤ ∑ τ ∈ S, (qp_straddleEdges K₀ (fun u => tag u = τ)).card := by
-- proof
  apply StatMech.FK.ecz_peel_le K₀ tag p q hp hp1 hq

/--
[ecz_block_fkZEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_block_fkZEdge_eq
  {d K : ℕ}
  {s : Fin d → Bool}
  {p q : ℝ} :
-- imply
  ecz_fkZEdge (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) (some s)) p q = ecz_fkZEdge (boxGraph d K) p q := by
-- proof
  apply StatMech.FK.ecz_block_fkZEdge d K s p q

/--
[ecz_box_neglog_doubling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_box_neglog_doubling_eq
  {d K : ℕ}
  {t : ℝ} :
-- imply
  ecz_u d t (2 * K + 1) ≤ (2 : ℝ) ^ d * ecz_u d t K + ((2 * d * (qp_Jset d K).card + (2 ^ d + 1) * (2 * d * (qp_Jset d K).card) : ℕ) : ℝ) * (-Real.log (1 - fsc_logistic t)) := by
-- proof
  apply StatMech.FK.ecz_box_neglog_doubling d K t

/--
[ecz_ivp2_eq_edgeFE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_ivp2_eq_edgeFE_eq
  {d : ℕ}
  {t : ℝ}
  {n : ℕ}
-- given
  (hE : 0 < (boxGraph d n).edgeFinset.card) :
-- imply
  ivp2_tiltFreeEnergy (boxGraph d n) 2 t = (ecz_NE (boxGraph d n) : ℝ) / ((boxGraph d n).edgeFinset.card : ℝ) * Real.log 2 + ecz_edgeFreeEnergy d t n := by
-- proof
  apply StatMech.FK.ecz_ivp2_eq_edgeFE t n hE

/--
[ecz_centered_eq_cfe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_centered_eq_cfe_eq
  {d : ℕ}
  {t : ℝ}
  {n : ℕ}
-- given
  (hE : 0 < (boxGraph d n).edgeFinset.card) :
-- imply
  cfe_centered (boxGraph d n) 2 t = ecz_edgeFreeEnergy d t n - ecz_edgeFreeEnergy d 0 n := by
-- proof
  apply StatMech.FK.ecz_centered_eq_cfe t n hE

/--
[ecz_edgeFE_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_edgeFE_eq_eq
  {d : ℕ}
  {t : ℝ}
  {n : ℕ} :
-- imply
  ecz_edgeFreeEnergy d t n = -(ecz_u d t n / agl_E d n) + Real.log (1 + Real.exp t) := by
-- proof
  apply StatMech.FK.ecz_edgeFE_eq t n

/--
[ecz_additiveDoublingBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_additiveDoublingBound_eq
  {d : ℕ}
  {d : ℕ}
  {t : ℝ}
-- given
  (hd : 1 ≤ d) :
-- imply
  ecz_AdditiveDoublingBound d t := by
-- proof
  apply StatMech.FK.ecz_additiveDoublingBound d hd t

/--
[ecz_numClusters_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_numClusters_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  numClusters G ω ≤ Fintype.card V := by
-- proof
  apply StatMech.FK.ecz_numClusters_le G ω

/--
[ecz_fkWeight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_fkWeight_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  fkWeight G p 2 ω ≤ 2 ^ Fintype.card V := by
-- proof
  apply StatMech.FK.ecz_fkWeight_le G hp hp1 ω

/--
[ecz_closedOff_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_closedOff_card_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  Fintype.card (ecz_ClosedOff G) = 2 ^ G.edgeFinset.card := by
-- proof
  apply StatMech.FK.ecz_closedOff_card G

/--
[ecz_fkZEdge_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_fkZEdge_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  ecz_fkZEdge G p 2 ≤ (2 : ℝ) ^ G.edgeFinset.card * 2 ^ Fintype.card V := by
-- proof
  apply StatMech.FK.ecz_fkZEdge_le G hp hp1

/--
[ecz_box_edge_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_box_edge_pos_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (hd : 1 ≤ d)
  (hn : 1 ≤ n) :
-- imply
  0 < (boxGraph d n).edgeFinset.card := by
-- proof
  apply StatMech.FK.ecz_box_edge_pos d hd hn

/--
[ecz_boxVerts_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_boxVerts_card_eq
  {d n : ℕ} :
-- imply
  Fintype.card (boxVerts d n) = (2 * n + 1) ^ d := by
-- proof
  apply StatMech.FK.ecz_boxVerts_card d n

/--
[ecz_boxVerts_le_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_boxVerts_le_edges_eq
  {d n : ℕ}
-- given
  (hd : 1 ≤ d)
  (hn : 1 ≤ n) :
-- imply
  Fintype.card (boxVerts d n) ≤ 2 * (boxGraph d n).edgeFinset.card := by
-- proof
  apply StatMech.FK.ecz_boxVerts_le_edges d n hd hn

/--
[ecz_edgeFE_le_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_edgeFE_le_const_eq
  {d n : ℕ}
  {s : ℝ}
-- given
  (hd : 1 ≤ d)
  (hn : 1 ≤ n)
  (hE : 0 < (boxGraph d n).edgeFinset.card) :
-- imply
  ecz_edgeFreeEnergy d s n ≤ 3 * Real.log 2 + Real.log (1 + Real.exp s) := by
-- proof
  apply StatMech.FK.ecz_edgeFE_le_const d n hd hn s hE

/--
[ecz_box_nesting_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_box_nesting_le_eq
  {d : ℕ}
  {a n : ℕ}
  {t : ℝ}
-- given
  (hle : a ≤ n) :
-- imply
  ecz_u d t n ≤ ecz_u d t a + ((agl_interfaceCard (boxGraph d n) (ecz_subBoxPred d a n) + ((agl_right (boxGraph d n) (ecz_subBoxPred d a n)).edgeFinset.card : ℝ))) * (-Real.log (1 - fsc_logistic t)) := by
-- proof
  apply StatMech.FK.ecz_box_nesting_le a n hle t

/--
[ecz_sum_edgeFinset_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_sum_edgeFinset_card_eq
  {d : ℕ}
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {G : SimpleGraph V}
  {H : SimpleGraph W}
  [DecidableRel G.Adj]
  [DecidableRel H.Adj] :
-- imply
  (G ⊕g H).edgeFinset.card = G.edgeFinset.card + H.edgeFinset.card := by
-- proof
  apply StatMech.FK.ecz_sum_edgeFinset_card G H

/--
[ecz_partition_edge_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_partition_edge_card_eq
  {d : ℕ}
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  [DecidablePred P]
-- given
  (P : U → Prop) :
-- imply
  K₀.edgeFinset.card = (agl_left K₀ P).edgeFinset.card + (agl_right K₀ P).edgeFinset.card + agl_interfaceCard K₀ P := by
-- proof
  apply StatMech.FK.ecz_partition_edge_card K₀ P

/--
[ecz_peel_edge_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_peel_edge_card_eq
  {d : ℕ}
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  {τ : T}
  {S : Finset T}
-- given
  (hτ : τ ∉ S) :
-- imply
  (qp_restG K₀ tag (insert τ S)).edgeFinset.card = (qp_blkG K₀ tag τ).edgeFinset.card + (qp_restG K₀ tag S).edgeFinset.card + agl_interfaceCard (qp_restG K₀ tag (insert τ S)) (fun x => tag x.1 = τ) := by
-- proof
  apply StatMech.FK.ecz_peel_edge_card K₀ τ S hτ

/--
[ecz_multiblock_subadd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_multiblock_subadd_eq
  {d : ℕ}
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  ∀ S : Finset T, ecz_uu (qp_restG K₀ tag S) p q ≤ (∑ τ ∈ S, ecz_uu (qp_blkG K₀ tag τ) p q) + (((qp_restG K₀ tag S).edgeFinset.card : ℝ) - ∑ τ ∈ S, ((qp_blkG K₀ tag τ).edgeFinset.card : ℝ)) * (-Real.log (1 - p)) := by
-- proof
  apply StatMech.FK.ecz_multiblock_subadd K₀ p q hp hp1 hq

/--
[ecz_box_annulus_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_box_annulus_card_eq
  {d : ℕ}
  {a n : ℕ}
-- given
  (hle : a ≤ n) :
-- imply
  (agl_interfaceCard (boxGraph d n) (ecz_subBoxPred d a n) + (agl_right (boxGraph d n) (ecz_subBoxPred d a n)).edgeFinset.card) + (boxGraph d a).edgeFinset.card = (boxGraph d n).edgeFinset.card := by
-- proof
  apply StatMech.FK.ecz_box_annulus_card a n hle

/--
[ecz_box_nesting_le'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_box_nesting_le'_eq
  {d : ℕ}
  {a n : ℕ}
  {t : ℝ}
-- given
  (hle : a ≤ n) :
-- imply
  ecz_u d t n ≤ ecz_u d t a + (((boxGraph d n).edgeFinset.card : ℝ) - ((boxGraph d a).edgeFinset.card : ℝ)) * (-Real.log (1 - fsc_logistic t)) := by
-- proof
  apply StatMech.FK.ecz_box_nesting_le' a n hle t

/--
[ecz_box_nesting_sandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_box_nesting_sandwich_eq
  {d : ℕ}
  {a n b : ℕ}
  {t : ℝ}
-- given
  (han : a ≤ n)
  (hnb : n ≤ b) :
-- imply
  ecz_u d t b - ((agl_interfaceCard (boxGraph d b) (ecz_subBoxPred d n b) + ((agl_right (boxGraph d b) (ecz_subBoxPred d n b)).edgeFinset.card : ℝ))) * (-Real.log (1 - fsc_logistic t)) ≤ ecz_u d t n ∧ ecz_u d t n ≤ ecz_u d t a + ((agl_interfaceCard (boxGraph d n) (ecz_subBoxPred d a n) + ((agl_right (boxGraph d n) (ecz_subBoxPred d a n)).edgeFinset.card : ℝ))) * (-Real.log (1 - fsc_logistic t)) := by
-- proof
  apply StatMech.FK.ecz_box_nesting_sandwich a n b han hnb t

/--
[ecz_box_nesting_sandwich'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_box_nesting_sandwich'_eq
  {d : ℕ}
  {a n b : ℕ}
  {t : ℝ}
-- given
  (han : a ≤ n)
  (hnb : n ≤ b) :
-- imply
  ecz_u d t b - (((boxGraph d b).edgeFinset.card : ℝ) - ((boxGraph d n).edgeFinset.card : ℝ)) * (-Real.log (1 - fsc_logistic t)) ≤ ecz_u d t n ∧ ecz_u d t n ≤ ecz_u d t a + (((boxGraph d n).edgeFinset.card : ℝ) - ((boxGraph d a).edgeFinset.card : ℝ)) * (-Real.log (1 - fsc_logistic t)) := by
-- proof
  apply StatMech.FK.ecz_box_nesting_sandwich' a n b han hnb t

/--
[ecz_T_mul_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_T_mul_le_eq
  {d : ℕ}
  {d : ℕ}
  {m n : ℕ} :
-- imply
  ecz_T m n * (2 * m + 1) ≤ 2 * n + 1 := by
-- proof
  apply StatMech.FK.ecz_T_mul_le m n

/--
[ecz_center_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_center_mem_box_eq
  {d : ℕ}
  {d : ℕ}
  {m n : ℕ}
  {c : Fin d → Fin (ecz_T m n)}
  {y : Site d}
-- given
  (hy : y ∈ box d m) :
-- imply
  (fun i => y i + ecz_center m n c i) ∈ box d n := by
-- proof
  apply StatMech.FK.ecz_center_mem_box m n c y hy

/--
[ecz_vanHoveTag_eq_some_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_vanHoveTag_eq_some_iff_eq
  {d : ℕ}
  {d : ℕ}
  {m n : ℕ}
  {x : boxVerts d n}
  {c : Fin d → Fin (ecz_T m n)} :
-- imply
  ecz_vanHoveTag m n x = some c ↔ ∀ i, ((x : Site d) i - ecz_center m n c i).natAbs ≤ m := by
-- proof
  apply StatMech.FK.ecz_vanHoveTag_eq_some_iff m n x c

/--
[ecz_cellBlock_fkZEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_cellBlock_fkZEdge_eq
  {d : ℕ}
  {d : ℕ}
  {m n : ℕ}
  {c : Fin d → Fin (ecz_T m n)}
  {p q : ℝ} :
-- imply
  ecz_fkZEdge (qp_blkG (boxGraph d n) (ecz_vanHoveTag m n) (some c)) p q = ecz_fkZEdge (boxGraph d m) p q := by
-- proof
  apply StatMech.FK.ecz_cellBlock_fkZEdge m n c p q

/--
[ecz_cellBlock_edge_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_cellBlock_edge_card_eq
  {d : ℕ}
  {d : ℕ}
  {m n : ℕ}
  {c : Fin d → Fin (ecz_T m n)} :
-- imply
  (qp_blkG (boxGraph d n) (ecz_vanHoveTag m n) (some c)).edgeFinset.card = (boxGraph d m).edgeFinset.card := by
-- proof
  apply StatMech.FK.ecz_cellBlock_edge_card m n c

/--
[ecz_cell_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_cell_card_eq
  {d : ℕ}
  {d : ℕ}
  {m n : ℕ} :
-- imply
  Fintype.card (Fin d → Fin (ecz_T m n)) = (ecz_T m n) ^ d := by
-- proof
  apply StatMech.FK.ecz_cell_card m n

/--
[ecz_box_vanHove_subadd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_box_vanHove_subadd_eq
  {d : ℕ}
  {d : ℕ}
  {m n : ℕ}
  {t : ℝ} :
-- imply
  ecz_u d t n ≤ ((ecz_T m n) ^ d : ℝ) * ecz_u d t m + (((boxGraph d n).edgeFinset.card : ℝ) - ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ)) * (-Real.log (1 - fsc_logistic t)) := by
-- proof
  apply StatMech.FK.ecz_box_vanHove_subadd m n t

/--
[ecz_denom_tendsto_atTop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_denom_tendsto_atTop_eq
  {d : ℕ}
  {d : ℕ} :
-- imply
  Tendsto (fun n : ℕ => (2 * (n : ℝ) + 1)) atTop atTop := by
-- proof
  apply StatMech.FK.ecz_denom_tendsto_atTop

/--
[ecz_packing_ratio_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_packing_ratio_tendsto_eq
  {d : ℕ}
  {d : ℕ}
  {m : ℕ} :
-- imply
  Tendsto (fun n => ((ecz_T m n : ℝ) * (2 * m + 1)) / (2 * n + 1)) atTop (𝓝 1) := by
-- proof
  apply StatMech.FK.ecz_packing_ratio_tendsto m

/--
[ecz_oddEven_ratio_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_oddEven_ratio_tendsto_eq
  {d : ℕ}
  {d : ℕ} :
-- imply
  Tendsto (fun n : ℕ => (2 * (n : ℝ) + 1) / (2 * n)) atTop (𝓝 1) := by
-- proof
  apply StatMech.FK.ecz_oddEven_ratio_tendsto

/--
[ecz_bulkFraction_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_bulkFraction_tendsto_eq
  {d : ℕ}
  {d : ℕ}
  {m : ℕ}
-- given
  (hd : 1 ≤ d)
  (hm : 1 ≤ m) :
-- imply
  Tendsto (fun n => ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ) / ((boxGraph d n).edgeFinset.card : ℝ)) atTop (𝓝 (2 * (m : ℝ) / (2 * m + 1))) := by
-- proof
  apply StatMech.FK.ecz_bulkFraction_tendsto hd m hm

/--
[ecz_perEdge_vanHove](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_perEdge_vanHove_eq
  {d : ℕ}
  {d : ℕ}
  {m n : ℕ}
  {s : ℝ}
-- given
  (hEn : 0 < (boxGraph d n).edgeFinset.card)
  (hEm : 0 < (boxGraph d m).edgeFinset.card) :
-- imply
  ecz_f d s n ≤ (((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ) / ((boxGraph d n).edgeFinset.card : ℝ)) * ecz_f d s m + (1 - ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ) / ((boxGraph d n).edgeFinset.card : ℝ)) * (-Real.log (1 - fsc_logistic s)) := by
-- proof
  apply StatMech.FK.ecz_perEdge_vanHove m n s hEn hEm

/--
[ecz_dyadic_f_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_dyadic_f_tendsto_eq
  {d : ℕ}
  {d : ℕ}
  {s : ℝ}
-- given
  (hd : 1 ≤ d)
  (hbox : ∀ j, 0 < (boxGraph d (agl_K j)).edgeFinset.card) :
-- imply
  ∃ L : ℝ, Tendsto (fun j => ecz_f d s (agl_K j)) atTop (𝓝 L) := by
-- proof
  apply StatMech.FK.ecz_dyadic_f_tendsto hd s hbox

/--
[ecz_f_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_f_bounds_eq
  {d : ℕ}
  {d : ℕ}
  {s : ℝ}
  {n : ℕ}
-- given
  (hd : 1 ≤ d)
  (hn : 1 ≤ n)
  (hEn : 0 < (boxGraph d n).edgeFinset.card) :
-- imply
  -(3 * Real.log 2) ≤ ecz_f d s n ∧ ecz_f d s n ≤ -Real.log (1 - fsc_logistic s) := by
-- proof
  apply StatMech.FK.ecz_f_bounds hd s n hn hEn

/--
[ecz_f_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_f_lower_eq
  {d : ℕ}
  {d : ℕ}
  {s : ℝ}
  {n : ℕ}
  {L : ℝ}
-- given
  (hd : 1 ≤ d)
  (hn : 1 ≤ n)
  (hbox : ∀ k, 1 ≤ k → 0 < (boxGraph d k).edgeFinset.card)
  (hL : Tendsto (fun j => ecz_f d s (agl_K j)) atTop (𝓝 L)) :
-- imply
  ((2 * (n : ℝ) + 1) / (2 * n)) * L - (-Real.log (1 - fsc_logistic s)) / (2 * n) ≤ ecz_f d s n := by
-- proof
  apply StatMech.FK.ecz_f_lower hd s n hn hbox L hL

/--
[ecz_g_dyadic_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_g_dyadic_tendsto_eq
  {d : ℕ}
  {d : ℕ}
  {s : ℝ}
  {L : ℝ}
-- given
  (hL : Tendsto (fun j => ecz_f d s (agl_K j)) atTop (𝓝 L)) :
-- imply
  Tendsto (fun j => ecz_g d s (agl_K j)) atTop (𝓝 L) := by
-- proof
  apply StatMech.FK.ecz_g_dyadic_tendsto s L hL

/--
[ecz_upperSeq_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_upperSeq_tendsto_eq
  {d : ℕ}
  {d : ℕ}
  {s : ℝ}
  {m : ℕ}
-- given
  (hd : 1 ≤ d)
  (hm : 1 ≤ m) :
-- imply
  Tendsto (fun n => (((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ) / ((boxGraph d n).edgeFinset.card : ℝ)) * ecz_f d s m + (1 - ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ) / ((boxGraph d n).edgeFinset.card : ℝ)) * (-Real.log (1 - fsc_logistic s))) atTop (𝓝 (ecz_g d s m)) := by
-- proof
  apply StatMech.FK.ecz_upperSeq_tendsto hd s m hm

/--
[ecz_perEdgeDensityConverges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_perEdgeDensityConverges_eq
  {d : ℕ}
  {d : ℕ}
  {s : ℝ}
-- given
  (hd : 1 ≤ d)
  (hbox : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card) :
-- imply
  ecz_PerEdgeDensityConverges d s := by
-- proof
  apply StatMech.FK.ecz_perEdgeDensityConverges hd s hbox

/--
[ecz_freeBulkCollapse_n1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_freeBulkCollapse_n1_eq
  {d : ℕ}
  {t : ℝ}
  {L : ℝ}
  {In : (n : ℕ) → Finset (Sym2 (boxVerts d n))}
  {δ : ℕ → ℝ}
-- given
  (hbox1 : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card)
  (hL0 : 0 ≤ L)
  (hL1 : L ≤ 1)
  (hIE : ∀ n, In n ⊆ (boxGraph d n).edgeFinset)
  (hδ0 : ∀ n, 0 ≤ δ n)
  (hδlim : Tendsto δ atTop (𝓝 0))
  (hin : ∀ n, ∀ e ∈ In n, |edgeMargProb (fkProb (boxGraph d n) (fsc_logistic t) 2) e - L| ≤ δ n)
  (hbdy : Tendsto (fun n => (((boxGraph d n).edgeFinset.card - (In n).card : ℝ)) / (boxGraph d n).edgeFinset.card) atTop (𝓝 0)) :
-- imply
  Tendsto (fun n => fpd_avgDensity (boxGraph d n) t) atTop (𝓝 L) := by
-- proof
  apply StatMech.FK.ecz_freeBulkCollapse_n1 t hbox1 L hL0 hL1 In hIE δ hδ0 hδlim hin hbdy

/--
[ecz_wiredBulkCollapse_n1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_wiredBulkCollapse_n1_eq
  {d : ℕ}
  {t : ℝ}
  {L : ℝ}
  {In : (n : ℕ) → Finset (Sym2 (boxVerts d n))}
  {δ : ℕ → ℝ}
-- given
  (hbox1 : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card)
  (hL0 : 0 ≤ L)
  (hL1 : L ≤ 1)
  (hIE : ∀ n, In n ⊆ (boxGraph d n).edgeFinset)
  (hδ0 : ∀ n, 0 ≤ δ n)
  (hδlim : Tendsto δ atTop (𝓝 0))
  (hin : ∀ n, ∀ e ∈ In n, |edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) (fsc_logistic t) 2) e - L| ≤ δ n)
  (hbdy : Tendsto (fun n => (((boxGraph d n).edgeFinset.card - (In n).card : ℝ)) / (boxGraph d n).edgeFinset.card) atTop (𝓝 0)) :
-- imply
  Tendsto (fun n => wpd_avgWiredDensity (boxGraph d n) (boxBoundary d n) 2 t) atTop (𝓝 L) := by
-- proof
  apply StatMech.FK.ecz_wiredBulkCollapse_n1 t hbox1 L hL0 hL1 In hIE δ hδ0 hδlim hin hbdy

/--
[ecz_genuineFreeCollapse_n1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_genuineFreeCollapse_n1_eq
  {d : ℕ}
  {N : ℕ}
-- given
  (hd : 1 ≤ d)
  (hbox1 : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card) :
-- imply
  fpe2_GenuineFreeCollapse (d := d) N := by
-- proof
  apply StatMech.FK.ecz_genuineFreeCollapse_n1 hd N hbox1

/--
[ecz_genuineWiredCollapse_n1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_genuineWiredCollapse_n1_eq
  {d : ℕ}
  {N : ℕ}
-- given
  (hd : 1 ≤ d)
  (hbox1 : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card) :
-- imply
  fpe2_GenuineWiredCollapse (d := d) N := by
-- proof
  apply StatMech.FK.ecz_genuineWiredCollapse_n1 hd N hbox1

/--
[ecz_wiredCentered_tendsto_n1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_wiredCentered_tendsto_n1_eq
  {d : ℕ}
  {G : ℝ → ℝ}
  {t : ℝ}
-- given
  (hd : 1 ≤ d)
  (hbox1 : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card)
  (hfree : Tendsto (fun n => cfe_centered (boxGraph d n) 2 t) atTop (𝓝 (G t))) :
-- imply
  Tendsto (fun n => cfe_wiredCentered (boxGraph d n) (boxBoundary d n) 2 t) atTop (𝓝 (G t)) := by
-- proof
  apply StatMech.FK.ecz_wiredCentered_tendsto_n1 hd hbox1 t hfree

/--
[ecz_genuineFreeIsLeftDeriv_n1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_genuineFreeIsLeftDeriv_n1_eq
  {d : ℕ}
  {N : ℕ}
  {G : ℝ → ℝ}
-- given
  (hbox1 : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card)
  (hG : ConvexOn ℝ univ G)
  (hboxfree : ∀ t, Tendsto (fun n => cfe_centered (boxGraph d n) 2 t) atTop (𝓝 (G t)))
  (hcol : fpe2_GenuineFreeCollapse d N) :
-- imply
  fpe2_GenuineFreeIsLeftDeriv d N G := by
-- proof
  apply StatMech.FK.ecz_genuineFreeIsLeftDeriv_n1 N hbox1 hG hboxfree hcol

/--
[ecz_genuineWiredIsRightDeriv_n1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_genuineWiredIsRightDeriv_n1_eq
  {d : ℕ}
  {N : ℕ}
  {G : ℝ → ℝ}
-- given
  (hd : 1 ≤ d)
  (hbox1 : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card)
  (hG : ConvexOn ℝ univ G)
  (hboxfree : ∀ t, Tendsto (fun n => cfe_centered (boxGraph d n) 2 t) atTop (𝓝 (G t)))
  (hcolfree : fpe2_GenuineFreeCollapse d N)
  (hcolwired : fpe2_GenuineWiredCollapse d N) :
-- imply
  fpe2_GenuineWiredIsRightDeriv d N G := by
-- proof
  apply StatMech.FK.ecz_genuineWiredIsRightDeriv_n1 hd N hbox1 hG hboxfree hcolfree hcolwired

/--
[ecz_fk_uniqueness_of_centeredData_n1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_fk_uniqueness_of_centeredData_n1_eq
  {d : ℕ}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {G : ℝ → ℝ}
-- given
  (hd : 1 ≤ d)
  (heb : eb ∈ (boxGraph d N).edgeFinset)
  (hbox1 : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card)
  (hG : ConvexOn ℝ univ G)
  (hboxfree : ∀ t, Tendsto (fun n => cfe_centered (boxGraph d n) 2 t) atTop (𝓝 (G t))) :
-- imply
  {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧ eventMassProb (fuc_freeMass d N t) A ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable := by
-- proof
  apply StatMech.FK.ecz_fk_uniqueness_of_centeredData_n1 hd N eb heb hbox1 hG hboxfree

/--
[ecz_blockOscillation_satisfiable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_blockOscillation_satisfiable_eq
  {d : ℕ} :
-- imply
  ∃ (g : ℕ → ℝ) (bj : ℕ → ℕ) (osc : ℕ → ℝ), Tendsto bj atTop atTop ∧ Tendsto osc atTop (𝓝 0) ∧ (∀ n, |g n - g (agl_K (bj n))| ≤ osc (bj n)) := by
-- proof
  apply StatMech.FK.ecz_blockOscillation_satisfiable

/--
[ecz_blockOscillation_of_perEdgeDensity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_blockOscillation_of_perEdgeDensity_eq
  {d : ℕ}
  {s : ℝ}
-- given
  (hρ : ecz_PerEdgeDensityConverges d s) :
-- imply
  ecz_BlockOscillation d s := by
-- proof
  apply StatMech.FK.ecz_blockOscillation_of_perEdgeDensity s hρ

/--
[ecz_edgeFE_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_edgeFE_tendsto_eq
  {d : ℕ}
  {s : ℝ}
-- given
  (hd : 1 ≤ d)
  (hbox : ∀ j, 0 < (boxGraph d (agl_K j)).edgeFinset.card)
  (hosc : ecz_BlockOscillation d s) :
-- imply
  ∃ L : ℝ, Tendsto (fun n => ecz_edgeFreeEnergy d s n) atTop (𝓝 L) := by
-- proof
  apply StatMech.FK.ecz_edgeFE_tendsto hd s hbox hosc

/--
[ecz_cfe_centered_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_cfe_centered_tendsto_eq
  {d : ℕ}
  {t : ℝ}
-- given
  (hd : 1 ≤ d)
  (hbox : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card)
  (hosct : ecz_BlockOscillation d t)
  (hosc0 : ecz_BlockOscillation d 0) :
-- imply
  ∃ G : ℝ, Tendsto (fun n => cfe_centered (boxGraph d n) 2 t) atTop (𝓝 G) := by
-- proof
  apply StatMech.FK.ecz_cfe_centered_tendsto hd t hbox hosct hosc0

/--
[ecz_centeredConvergence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_centeredConvergence_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (hbox : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card)
  (hosc : ∀ s, ecz_BlockOscillation d s) :
-- imply
  ∃ G : ℝ → ℝ, (∀ t, Tendsto (fun n => cfe_centered (boxGraph d n) 2 t) atTop (𝓝 (G t))) ∧ ConvexOn ℝ Set.univ G ∧ G 0 = 0 := by
-- proof
  apply StatMech.FK.ecz_centeredConvergence hd hbox hosc

/--
[ecz_fk_uniqueness_of_blockOscillation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_fk_uniqueness_of_blockOscillation_eq
  {d : ℕ}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
-- given
  (hd : 1 ≤ d)
  (heb : eb ∈ (boxGraph d N).edgeFinset)
  (hEbox : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card)
  (hosc : ∀ s, ecz_BlockOscillation d s) :
-- imply
  {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧ eventMassProb (fuc_freeMass d N t) A ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable := by
-- proof
  apply StatMech.FK.ecz_fk_uniqueness_of_blockOscillation hd N eb heb hEbox hosc

/--
[ecz_fk_uniqueness_of_perEdgeDensity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_fk_uniqueness_of_perEdgeDensity_eq
  {d : ℕ}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
-- given
  (hd : 1 ≤ d)
  (heb : eb ∈ (boxGraph d N).edgeFinset)
  (hEbox : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card)
  (hρ : ∀ s, ecz_PerEdgeDensityConverges d s) :
-- imply
  {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧ eventMassProb (fuc_freeMass d N t) A ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable := by
-- proof
  apply StatMech.FK.ecz_fk_uniqueness_of_perEdgeDensity hd N eb heb hEbox hρ

/--
[ecz_fk_uniqueness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_fk_uniqueness_eq
  {d : ℕ}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
-- given
  (hd : 1 ≤ d)
  (heb : eb ∈ (boxGraph d N).edgeFinset) :
-- imply
  {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧ eventMassProb (fuc_freeMass d N t) A ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable := by
-- proof
  apply StatMech.FK.ecz_fk_uniqueness hd N eb heb

/--
[ecz_residue_remark](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean)
-/
@[path]
private lemma ecz_residue_remark_eq :
-- imply
  True := by
-- proof
  apply StatMech.FK.ecz_residue_remark


-- created on 2026-10-23
