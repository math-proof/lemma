import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc123assemble
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc123_cut_forces_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc123assemble.lean)
-/
@[path]
private lemma bc123_cut_forces_distinct_eq
  {d : ℕ}
  {G : SimpleGraph V}
  {u t₁ t₂ : V}
-- given
  (hcut : ¬ (G.deleteIncidenceSet u).Reachable t₁ t₂) :
-- imply
  t₁ ≠ t₂ := by
-- proof
  apply StatMech.Walls.bc123_cut_forces_distinct G hcut

/--
[bc123_within_hub_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc123assemble.lean)
-/
@[path]
private lemma bc123_within_hub_distinct_eq
  {d : ℕ}
  {G : SimpleGraph V}
  {u t₁ t₂ t₃ : V}
-- given
  (hc₁₂ : ¬ (G.deleteIncidenceSet u).Reachable t₁ t₂)
  (hc₁₃ : ¬ (G.deleteIncidenceSet u).Reachable t₁ t₃)
  (hc₂₃ : ¬ (G.deleteIncidenceSet u).Reachable t₂ t₃) :
-- imply
  t₁ ≠ t₂ ∧ t₁ ≠ t₃ ∧ t₂ ≠ t₃ := by
-- proof
  apply StatMech.Walls.bc123_within_hub_distinct G hc₁₂ hc₁₃ hc₂₃

/--
[bc123_count_tolerates_shared_leaves](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc123assemble.lean)
-/
@[path]
private lemma bc123_count_tolerates_shared_leaves_eq
  {d : ℕ}
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (hacyc : G.IsAcyclic)
  (hmin : ∀ v, 1 ≤ G.degree v) :
-- imply
  (univ.filter (fun v => 3 ≤ G.degree v)).card ≤ (univ.filter (fun v => G.degree v = 1)).card := by
-- proof
  apply StatMech.Walls.bc123_count_tolerates_shared_leaves G hacyc hmin

/--
[bc123_shared_tip_breaks_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc123assemble.lean)
-/
@[path]
private lemma bc123_shared_tip_breaks_cut_eq
  {d : ℕ} :
-- imply
  ((SimpleGraph.fromEdgeSet {s((0 : Fin 3), 2), s((1 : Fin 3), 2)}).deleteIncidenceSet (0 : Fin 3)).Reachable 2 1 := by
-- proof
  apply StatMech.Walls.bc123_shared_tip_breaks_cut

/--
[bc123_gap1_finiteCarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc123assemble.lean)
-/
@[path]
private lemma bc123_gap1_finiteCarrier_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (hd : 1 ≤ d)
  (hL : 3 ≤ L) :
-- imply
  bc112_SeparatedArmGraph ω L R := by
-- proof
  apply StatMech.Walls.bc123_gap1_finiteCarrier hd ω L R hL

/--
[bc123_count_from_boundaryLeafResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc123assemble.lean)
-/
@[path]
private lemma bc123_count_from_boundaryLeafResidue_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc112_BoundaryLeafResidue ω L R) :
-- imply
  bc106_separatedTcount ω L R ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc123_count_from_boundaryLeafResidue ω L R h

/--
[bc123_separatedCount_closes_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc123assemble.lean)
-/
@[path]
private lemma bc123_separatedCount_closes_of_residue_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ} :
-- imply
  bc112_BoundaryLeafResidue ω L R → (bc106_SeparatedContractedTrifGraph ω L R ∧ bc106_separatedTcount ω L R ≤ boxSV_boundaryCard d R) := by
-- proof
  apply StatMech.Walls.bc123_separatedCount_closes_of_residue ω L R

/--
[bc123_globalForest_via_peel2_finiteCarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc123assemble.lean)
-/
@[path]
private lemma bc123_globalForest_via_peel2_finiteCarrier_eq
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
  (harmAdj : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∃ t₁ t₂ t₃ : (↑S : Type), bc121_Protected ω L R ιU t₁ ∧ bc121_Protected ω L R ιU t₂ ∧ bc121_Protected ω L R ιU t₃ ∧ G.Adj (ιU y) t₁ ∧ G.Adj (ιU y) t₂ ∧ G.Adj (ιU y) t₃ ∧ ¬ (G.deleteIncidenceSet (ιU y)).Reachable t₁ t₂ ∧ ¬ (G.deleteIncidenceSet (ιU y)).Reachable t₁ t₃ ∧ ¬ (G.deleteIncidenceSet (ιU y)).Reachable t₂ t₃)
  (hinj : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box d R → bc67_IsGnTrifurcation ω L z → ιU y = ιU z → y = z)
  (hFmin : ∀ (F : SimpleGraph (↑S : Type)) [DecidableRel F.Adj], F ≤ G → F.IsAcyclic → (∀ v : (↑S : Type), F.degree v = 1 → bc121_Protected ω L R ιU v) → (∀ a b : (↑S : Type), bc121_Protected ω L R ιU a → bc121_Protected ω L R ιU b → G.Reachable a b → F.Reachable a b) → ∀ v : (↑S : Type), 1 ≤ F.degree v) :
-- imply
  bc69_Gn_globalForest ω L R := by
-- proof
  apply StatMech.Walls.bc123_globalForest_via_peel2_finiteCarrier ω L R G hGac ιU harmAdj hinj hFmin

/--
[bc123_count_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc123assemble.lean)
-/
@[path]
private lemma bc123_count_nonvacuous_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {z₀ z₁ : Site d}
-- given
  (hz₀ : z₀ ∈ vertexBoundary d R)
  (hz₁ : z₁ ∈ vertexBoundary d R)
  (hzne : z₀ ≠ z₁)
  (hno : ∀ y, y ∈ box d R → ¬ bc106_SeparatedCoarseTrif ω L y) :
-- imply
  bc106_separatedTcount ω L R ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc123_count_nonvacuous ω L R hz₀ hz₁ hzne hno

/--
[bc123_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc123assemble.lean)
-/
@[path]
private lemma bc123_status_eq
  {d : ℕ} :
-- imply
  (∀ {V : Type} (G : SimpleGraph V) (u t₁ t₂ t₃ : V), ¬ (G.deleteIncidenceSet u).Reachable t₁ t₂ → ¬ (G.deleteIncidenceSet u).Reachable t₁ t₃ → ¬ (G.deleteIncidenceSet u).Reachable t₂ t₃ → t₁ ≠ t₂ ∧ t₁ ≠ t₃ ∧ t₂ ≠ t₃) ∧ (∀ {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj], G.IsAcyclic → (∀ v, 1 ≤ G.degree v) → (univ.filter (fun v => 3 ≤ G.degree v)).card ≤ (univ.filter (fun v => G.degree v = 1)).card) ∧ (((SimpleGraph.fromEdgeSet {s((0 : Fin 3), 2), s((1 : Fin 3), 2)}).deleteIncidenceSet (0 : Fin 3)).Reachable 2 1) ∧ (∀ (hd : 1 ≤ d) (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), 3 ≤ L → bc112_SeparatedArmGraph ω L R) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), bc112_BoundaryLeafResidue ω L R → bc106_separatedTcount ω L R ≤ boxSV_boundaryCard d R) := by
-- proof
  apply StatMech.Walls.bc123_status


-- created on 2026-10-23
