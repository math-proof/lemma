import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bc64coarseembed
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc64_boxAround_disjoint_of_farCoord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc64coarseembed.lean)
-/
@[path]
private lemma bc64_boxAround_disjoint_of_farCoord_eq
  {d : ℕ}
  {L : ℕ}
  {y y' : Site d}
  {i : Fin d}
-- given
  (hfar : 2 * L < ((y - y') i).natAbs) :
-- imply
  Disjoint (bc61_boxAround d L y) (bc61_boxAround d L y') := by
-- proof
  apply StatMech.Walls.bc64_boxAround_disjoint_of_farCoord i hfar

/--
[bc64_boxAround_disjoint_of_far](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc64coarseembed.lean)
-/
@[path]
private lemma bc64_boxAround_disjoint_of_far_eq
  {d : ℕ}
  {L : ℕ}
  {y y' : Site d}
-- given
  (hfar : ∃ i, 2 * L < ((y - y') i).natAbs) :
-- imply
  Disjoint (bc61_boxAround d L y) (bc61_boxAround d L y') := by
-- proof
  apply StatMech.Walls.bc64_boxAround_disjoint_of_far hfar

/--
[bc64_notMem_both_of_far](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc64coarseembed.lean)
-/
@[path]
private lemma bc64_notMem_both_of_far_eq
  {d : ℕ}
  {L : ℕ}
  {y y' x : Site d}
  {i : Fin d}
-- given
  (hfar : 2 * L < ((y - y') i).natAbs)
  (hx : x ∈ bc61_boxAround d L y) :
-- imply
  x ∉ bc61_boxAround d L y' := by
-- proof
  apply StatMech.Walls.bc64_notMem_both_of_far i hfar hx

/--
[bc64_starG_isTree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc64coarseembed.lean)
-/
@[path]
private lemma bc64_starG_isTree_eq
  {d : ℕ} :
-- imply
  bc64_starG.IsTree := by
-- proof
  apply StatMech.Walls.bc64_starG_isTree

/--
[bc64_starG_centre_deg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc64coarseembed.lean)
-/
@[path]
private lemma bc64_starG_centre_deg_eq
  {d : ℕ} :
-- imply
  bc64_starG.degree 0 = 3 := by
-- proof
  apply StatMech.Walls.bc64_starG_centre_deg

/--
[bc64_starG_leaf_deg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc64coarseembed.lean)
-/
@[path]
private lemma bc64_starG_leaf_deg_eq
  {d : ℕ} :
-- imply
  ∀ i : Fin 4, i ≠ 0 → bc64_starG.degree i = 1 := by
-- proof
  apply StatMech.Walls.bc64_starG_leaf_deg

/--
[bc64_starG_deg1_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc64coarseembed.lean)
-/
@[path]
private lemma bc64_starG_deg1_iff_eq
  {d : ℕ}
  {i : Fin 4} :
-- imply
  bc64_starG.degree i = 1 ↔ i ≠ 0 := by
-- proof
  apply StatMech.Walls.bc64_starG_deg1_iff i

/--
[bc64_starForest_adj_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc64coarseembed.lean)
-/
@[path]
private lemma bc64_starForest_adj_iff_eq
  {d : ℕ}
  {β : Type}
  {p q : β × Fin 4} :
-- imply
  (bc64_starForest β).Adj p q ↔ (p.1 = q.1 ∧ bc64_starG.Adj p.2 q.2) := by
-- proof
  apply StatMech.Walls.bc64_starForest_adj_iff

/--
[bc64_starForest_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc64coarseembed.lean)
-/
@[path]
private lemma bc64_starForest_fst_eq
  {d : ℕ}
  {β : Type}
  {p q : β × Fin 4}
-- given
  (h : (bc64_starForest β).Adj p q) :
-- imply
  p.1 = q.1 := by
-- proof
  apply StatMech.Walls.bc64_starForest_fst h

/--
[bc64_walk_fst_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc64coarseembed.lean)
-/
@[path]
private lemma bc64_walk_fst_const_eq
  {d : ℕ}
  {β : Type}
  {p q : β × Fin 4}
  {w : (bc64_starForest β).Walk p q} :
-- imply
  ∀ v ∈ w.support, v.1 = p.1 := by
-- proof
  apply StatMech.Walls.bc64_walk_fst_const w

/--
[bc64_snd_injOn_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc64coarseembed.lean)
-/
@[path]
private lemma bc64_snd_injOn_support_eq
  {d : ℕ}
  {β : Type}
  {v : β × Fin 4}
  {c : (bc64_starForest β).Walk v v} :
-- imply
  Set.InjOn (Prod.snd : β × Fin 4 → Fin 4) {x | x ∈ c.support} := by
-- proof
  apply StatMech.Walls.bc64_snd_injOn_support c

/--
[bc64_starForest_acyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc64coarseembed.lean)
-/
@[path]
private lemma bc64_starForest_acyclic_eq
  {d : ℕ}
  {β : Type} :
-- imply
  (bc64_starForest β).IsAcyclic := by
-- proof
  apply StatMech.Walls.bc64_starForest_acyclic β

/--
[bc64_starForest_neighborFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc64coarseembed.lean)
-/
@[path]
private lemma bc64_starForest_neighborFinset_eq
  {d : ℕ}
  {β : Type}
  [DecidableEq β]
  [Fintype β]
  {t : β}
  {i : Fin 4} :
-- imply
  (bc64_starForest β).neighborFinset (t, i) = ({t} : Finset β) ×ˢ (bc64_starG.neighborFinset i) := by
-- proof
  apply StatMech.Walls.bc64_starForest_neighborFinset t i

/--
[bc64_starForest_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc64coarseembed.lean)
-/
@[path]
private lemma bc64_starForest_degree_eq
  {d : ℕ}
  {β : Type}
  [DecidableEq β]
  [Fintype β]
  {t : β}
  {i : Fin 4} :
-- imply
  (bc64_starForest β).degree (t, i) = bc64_starG.degree i := by
-- proof
  apply StatMech.Walls.bc64_starForest_degree t i

/--
[bc64_starForest_min_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc64coarseembed.lean)
-/
@[path]
private lemma bc64_starForest_min_degree_eq
  {d : ℕ}
  {β : Type}
  [DecidableEq β]
  [Fintype β]
  {v : β × Fin 4} :
-- imply
  1 ≤ (bc64_starForest β).degree v := by
-- proof
  apply StatMech.Walls.bc64_starForest_min_degree v

/--
[bc64_starForest_deg1_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc64coarseembed.lean)
-/
@[path]
private lemma bc64_starForest_deg1_iff_eq
  {d : ℕ}
  {β : Type}
  [DecidableEq β]
  [Fintype β]
  {t : β}
  {i : Fin 4} :
-- imply
  (bc64_starForest β).degree (t, i) = 1 ↔ i ≠ 0 := by
-- proof
  apply StatMech.Walls.bc64_starForest_deg1_iff t i

/--
[bc64_coarseArmEmbedding_of_boundaryInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc64coarseembed.lean)
-/
@[path]
private lemma bc64_coarseArmEmbedding_of_boundaryInjection_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {z₀ z₁ : Site d}
-- given
  (hz₀ : z₀ ∈ vertexBoundary d R)
  (hz₁ : z₁ ∈ vertexBoundary d R)
  (hzne : z₀ ≠ z₁)
  (hinj : bc64_CoarseBoundaryInjection ω L R) :
-- imply
  bc63_CoarseArmEmbedding ω L R := by
-- proof
  apply StatMech.Walls.bc64_coarseArmEmbedding_of_boundaryInjection ω L R hz₀ hz₁ hzne hinj

/--
[bc64_coarseTcount_le_boundary_of_boundaryInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc64coarseembed.lean)
-/
@[path]
private lemma bc64_coarseTcount_le_boundary_of_boundaryInjection_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {z₀ z₁ : Site d}
-- given
  (hz₀ : z₀ ∈ vertexBoundary d R)
  (hz₁ : z₁ ∈ vertexBoundary d R)
  (hzne : z₀ ≠ z₁)
  (hinj : bc64_CoarseBoundaryInjection ω L R) :
-- imply
  bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc64_coarseTcount_le_boundary_of_boundaryInjection ω L R hz₀ hz₁ hzne hinj

/--
[bc64_disjointBoxes_multiTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc64coarseembed.lean)
-/
@[path]
private lemma bc64_disjointBoxes_multiTrif_eq
  {d : ℕ}
  {L : ℕ} :
-- imply
  Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) := by
-- proof
  apply StatMech.Walls.bc64_disjointBoxes_multiTrif L

/--
[bc64_disjointBoxes_sublattice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc64coarseembed.lean)
-/
@[path]
private lemma bc64_disjointBoxes_sublattice_eq
  {d : ℕ}
  {L : ℕ}
  {m m' : ℤ}
-- given
  (hmm : m ≠ m') :
-- imply
  Disjoint (bc61_boxAround 2 L (bc57_pt ((2 * (L : ℤ) + 1) * m) 0)) (bc61_boxAround 2 L (bc57_pt ((2 * (L : ℤ) + 1) * m') 0)) := by
-- proof
  apply StatMech.Walls.bc64_disjointBoxes_sublattice L hmm

/--
[bc64_line1_connected_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc64coarseembed.lean)
-/
@[path]
private lemma bc64_line1_connected_right_eq
  {d : ℕ}
  {a : ℤ}
  {j : ℕ} :
-- imply
  Connected 2 bc60_upperLines (bc57_pt a 1) (bc57_pt (a + (j : ℤ)) 1) := by
-- proof
  apply StatMech.Walls.bc64_line1_connected_right a j

/--
[bc64_line1_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc64coarseembed.lean)
-/
@[path]
private lemma bc64_line1_connected_eq
  {d : ℕ}
  {a b : ℤ} :
-- imply
  Connected 2 bc60_upperLines (bc57_pt a 1) (bc57_pt b 1) := by
-- proof
  apply StatMech.Walls.bc64_line1_connected a b

/--
[bc64_arms_can_share_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc64coarseembed.lean)
-/
@[path]
private lemma bc64_arms_can_share_boundary_eq
  {d : ℕ}
  {L : ℕ} :
-- imply
  Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧ Connected 2 bc60_upperLines (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1) := by
-- proof
  apply StatMech.Walls.bc64_arms_can_share_boundary L

/--
[bc64_infiniteClusters_top_null_of_boundaryInjection_route](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc64coarseembed.lean)
-/
@[path]
private lemma bc64_infiniteClusters_top_null_of_boundaryInjection_route_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (hfe : HasFiniteEnergyMerge μ)
  (hbdvertices : ∀ R : ℕ, ∃ z₀ z₁ : Site d, z₀ ∈ vertexBoundary d R ∧ z₁ ∈ vertexBoundary d R ∧ z₀ ≠ z₁)
  (hbinj : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc64_CoarseBoundaryInjection ω L R)
  (hcoarseRoute : 0 < μ {ω | numInfiniteClusters d ω = ⊤} → ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d, 0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
-- imply
  μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bc64_infiniteClusters_top_null_of_boundaryInjection_route μ hd hinv hfe L hbdvertices hbinj hcoarseRoute

/--
[bc64_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc64coarseembed.lean)
-/
@[path]
private lemma bc64_status_eq
  {d : ℕ} :
-- imply
  (∀ {L : ℕ} {y y' : Site d}, (∃ i, 2 * L < ((y - y') i).natAbs) → Disjoint (bc61_boxAround d L y) (bc61_boxAround d L y')) ∧ (∀ (β : Type), (bc64_starForest β).IsAcyclic) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (z₀ z₁ : Site d), z₀ ∈ vertexBoundary d R → z₁ ∈ vertexBoundary d R → z₀ ≠ z₁ → bc64_CoarseBoundaryInjection ω L R → bc63_CoarseArmEmbedding ω L R) ∧ (∀ (L : ℕ), Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧ Connected 2 bc60_upperLines (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1)) := by
-- proof
  apply StatMech.Walls.bc64_status


-- created on 2026-10-23
