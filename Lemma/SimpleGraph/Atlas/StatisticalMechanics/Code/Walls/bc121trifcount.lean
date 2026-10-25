import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc121trifcount.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc121_leaf_has_neighbour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc121trifcount.lean)
-/
@[path]
private lemma bc121_leaf_has_neighbour_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {v : V}
-- given
  (hv : G.degree v = 1) :
-- imply
  ∃ w, G.Adj v w := by
-- proof
  apply StatMech.Walls.bc121_leaf_has_neighbour G hv

/--
[bc121_leaf_neighbour_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc121trifcount.lean)
-/
@[path]
private lemma bc121_leaf_neighbour_unique_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {v w w' : V}
-- given
  (hv : G.degree v = 1)
  (hw : G.Adj v w)
  (hw' : G.Adj v w') :
-- imply
  w = w' := by
-- proof
  apply StatMech.Walls.bc121_leaf_neighbour_unique G hv hw hw'

/--
[bc121_leaf_delete_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc121trifcount.lean)
-/
@[path]
private lemma bc121_leaf_delete_reachable_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {v w : V}
  {a b : V}
-- given
  (hdeg : G.degree v = 1)
  (hvw : G.Adj v w)
  (ha : a ≠ v)
  (hb : b ≠ v)
  (hreach : G.Reachable a b) :
-- imply
  (G.deleteEdges {s(v, w)}).Reachable a b := by
-- proof
  apply StatMech.Walls.bc121_leaf_delete_reachable G hdeg hvw ha hb hreach

/--
[bc121_deleteEdge_card_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc121trifcount.lean)
-/
@[path]
private lemma bc121_deleteEdge_card_lt_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {v w : V}
  [DecidableRel (G.deleteEdges {s(v, w)}).Adj]
-- given
  (hvw : G.Adj v w) :
-- imply
  (G.deleteEdges {s(v, w)}).edgeFinset.card < G.edgeFinset.card := by
-- proof
  apply StatMech.Walls.bc121_deleteEdge_card_lt G hvw

/--
[bc121_deleteEdge_acyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc121trifcount.lean)
-/
@[path]
private lemma bc121_deleteEdge_acyclic_eq
  {d : ℕ}
  {G : SimpleGraph V}
  {s : Set (Sym2 V)}
-- given
  (hacyc : G.IsAcyclic) :
-- imply
  (G.deleteEdges s).IsAcyclic := by
-- proof
  apply StatMech.Walls.bc121_deleteEdge_acyclic G hacyc s

/--
[bc121_boundaryAnchored_subforest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc121trifcount.lean)
-/
@[path]
private lemma bc121_boundaryAnchored_subforest_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred B]
-- given
  (B : V → Prop)
  (hacyc : G.IsAcyclic) :
-- imply
  ∃ (F : SimpleGraph V) (_ : DecidableRel F.Adj), F ≤ G ∧ F.IsAcyclic ∧ (∀ v, F.degree v = 1 → B v) ∧ (∀ a b, B a → B b → G.Reachable a b → F.Reachable a b) := by
-- proof
  apply StatMech.Walls.bc121_boundaryAnchored_subforest G B hacyc

/--
[bc121_firstNeighbour_of_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc121trifcount.lean)
-/
@[path]
private lemma bc121_firstNeighbour_of_reachable_eq
  {d : ℕ}
  {F : SimpleGraph V}
  {u t : V}
-- given
  (hne : u ≠ t)
  (hreach : F.Reachable u t) :
-- imply
  ∃ w, F.Adj u w ∧ (F.deleteIncidenceSet u).Reachable w t := by
-- proof
  apply StatMech.Walls.bc121_firstNeighbour_of_reachable hne hreach

/--
[bc121_deg3_of_three_reached_targets](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc121trifcount.lean)
-/
@[path]
private lemma bc121_deg3_of_three_reached_targets_eq
  {d : ℕ}
  [Fintype V]
  {F : SimpleGraph V}
  [DecidableRel F.Adj]
  {u t₁ t₂ t₃ : V}
-- given
  (hne₁ : u ≠ t₁)
  (hne₂ : u ≠ t₂)
  (hne₃ : u ≠ t₃)
  (hr₁ : F.Reachable u t₁)
  (hr₂ : F.Reachable u t₂)
  (hr₃ : F.Reachable u t₃)
  (hcut₁₂ : ¬ (F.deleteIncidenceSet u).Reachable t₁ t₂)
  (hcut₁₃ : ¬ (F.deleteIncidenceSet u).Reachable t₁ t₃)
  (hcut₂₃ : ¬ (F.deleteIncidenceSet u).Reachable t₂ t₃) :
-- imply
  3 ≤ F.degree u := by
-- proof
  apply StatMech.Walls.bc121_deg3_of_three_reached_targets F hne₁ hne₂ hne₃ hr₁ hr₂ hr₃ hcut₁₂ hcut₁₃ hcut₂₃

/--
[bc121_globalForest_of_peel2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc121trifcount.lean)
-/
@[path]
private lemma bc121_globalForest_of_peel2_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {S : Set (Site d)}
  [hSfin : Fintype (↑S : Type)]
  [hSne : Nonempty (↑S : Type)]
  {G : SimpleGraph (↑S : Type)}
  [DecidableRel G.Adj]
  {ιU : Site d → (↑S : Type)}
-- given
  (hGac : G.IsAcyclic)
  (harm : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∃ t₁ t₂ t₃ : (↑S : Type), bc121_Protected ω L R ιU t₁ ∧ bc121_Protected ω L R ιU t₂ ∧ bc121_Protected ω L R ιU t₃ ∧ ιU y ≠ t₁ ∧ ιU y ≠ t₂ ∧ ιU y ≠ t₃ ∧ G.Reachable (ιU y) t₁ ∧ G.Reachable (ιU y) t₂ ∧ G.Reachable (ιU y) t₃ ∧ ¬ (G.deleteIncidenceSet (ιU y)).Reachable t₁ t₂ ∧ ¬ (G.deleteIncidenceSet (ιU y)).Reachable t₁ t₃ ∧ ¬ (G.deleteIncidenceSet (ιU y)).Reachable t₂ t₃)
  (hinj : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box d R → bc67_IsGnTrifurcation ω L z → ιU y = ιU z → y = z)
  (hFmin : ∀ (F : SimpleGraph (↑S : Type)) [DecidableRel F.Adj], F ≤ G → F.IsAcyclic → (∀ v : (↑S : Type), F.degree v = 1 → bc121_Protected ω L R ιU v) → (∀ a b : (↑S : Type), bc121_Protected ω L R ιU a → bc121_Protected ω L R ιU b → G.Reachable a b → F.Reachable a b) → ∀ v : (↑S : Type), 1 ≤ F.degree v) :
-- imply
  bc69_Gn_globalForest ω L R := by
-- proof
  apply StatMech.Walls.bc121_globalForest_of_peel2 ω L R G hGac ιU harm hinj hFmin

/--
[bc121_count_via_peel2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc121trifcount.lean)
-/
@[path]
private lemma bc121_count_via_peel2_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {S : Set (Site d)}
  [hSfin : Fintype (↑S : Type)]
  [hSne : Nonempty (↑S : Type)]
  {G : SimpleGraph (↑S : Type)}
  [DecidableRel G.Adj]
  {ιU : Site d → (↑S : Type)}
-- given
  (hGac : G.IsAcyclic)
  (harm : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∃ t₁ t₂ t₃ : (↑S : Type), bc121_Protected ω L R ιU t₁ ∧ bc121_Protected ω L R ιU t₂ ∧ bc121_Protected ω L R ιU t₃ ∧ ιU y ≠ t₁ ∧ ιU y ≠ t₂ ∧ ιU y ≠ t₃ ∧ G.Reachable (ιU y) t₁ ∧ G.Reachable (ιU y) t₂ ∧ G.Reachable (ιU y) t₃ ∧ ¬ (G.deleteIncidenceSet (ιU y)).Reachable t₁ t₂ ∧ ¬ (G.deleteIncidenceSet (ιU y)).Reachable t₁ t₃ ∧ ¬ (G.deleteIncidenceSet (ιU y)).Reachable t₂ t₃)
  (hinj : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box d R → bc67_IsGnTrifurcation ω L z → ιU y = ιU z → y = z)
  (hFmin : ∀ (F : SimpleGraph (↑S : Type)) [DecidableRel F.Adj], F ≤ G → F.IsAcyclic → (∀ v : (↑S : Type), F.degree v = 1 → bc121_Protected ω L R ιU v) → (∀ a b : (↑S : Type), bc121_Protected ω L R ιU a → bc121_Protected ω L R ιU b → G.Reachable a b → F.Reachable a b) → ∀ v : (↑S : Type), 1 ≤ F.degree v) :
-- imply
  bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc121_count_via_peel2 ω L R G hGac ιU harm hinj hFmin

/--
[bc121_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc121trifcount.lean)
-/
@[path]
private lemma bc121_nonvacuous_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {z₀ z₁ : Site d}
-- given
  (hz₀ : z₀ ∈ vertexBoundary d R)
  (hz₁ : z₁ ∈ vertexBoundary d R)
  (hzne : z₀ ≠ z₁)
  (hno : ∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) :
-- imply
  bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc121_nonvacuous ω L R hz₀ hz₁ hzne hno

/--
[bc121_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc121trifcount.lean)
-/
@[path]
private lemma bc121_status_eq
  {d : ℕ} :
-- imply
  (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (B : V → Prop) [DecidablePred B], G.IsAcyclic → ∃ (F : SimpleGraph V) (_ : DecidableRel F.Adj), F ≤ G ∧ F.IsAcyclic ∧ (∀ v, F.degree v = 1 → B v) ∧ (∀ a b, B a → B b → G.Reachable a b → F.Reachable a b)) ∧ (∀ {V : Type} [Fintype V] (F : SimpleGraph V) [DecidableRel F.Adj] (u t₁ t₂ t₃ : V), u ≠ t₁ → u ≠ t₂ → u ≠ t₃ → F.Reachable u t₁ → F.Reachable u t₂ → F.Reachable u t₃ → ¬ (F.deleteIncidenceSet u).Reachable t₁ t₂ → ¬ (F.deleteIncidenceSet u).Reachable t₁ t₃ → ¬ (F.deleteIncidenceSet u).Reachable t₂ t₃ → 3 ≤ F.degree u) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), bc69_Gn_globalForest ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) := by
-- proof
  apply StatMech.Walls.bc121_status


-- created on 2026-10-23
