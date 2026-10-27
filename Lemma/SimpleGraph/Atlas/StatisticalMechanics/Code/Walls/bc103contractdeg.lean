import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc103contractdeg.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc103_reachable_deleteIncidence_of_walk_avoiding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc103contractdeg.lean)
-/
@[path]
private lemma bc103_reachable_deleteIncidence_of_walk_avoiding_eq
  {d : ℕ}
  {G H : SimpleGraph V}
  {u : V}
  {a b : V}
  {p : H.Walk a b}
-- given
  (hHG : H ≤ G)
  (hp : ∀ x ∈ p.support, x ≠ u) :
-- imply
  (G.deleteIncidenceSet u).Reachable a b := by
-- proof
  apply StatMech.Walls.bc103_reachable_deleteIncidence_of_walk_avoiding hHG u p hp

/--
[bc103_firstNeighbour_of_arm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc103contractdeg.lean)
-/
@[path]
private lemma bc103_firstNeighbour_of_arm_eq
  {d : ℕ}
  {G F : SimpleGraph V}
  {u v : V}
-- given
  (hFG : F ≤ G)
  (hFreach : ∀ a b, G.Reachable a b → F.Reachable a b)
  (hadj : G.Adj u v) :
-- imply
  ∃ w, F.Adj u w ∧ (G.deleteIncidenceSet u).Reachable w v := by
-- proof
  apply StatMech.Walls.bc103_firstNeighbour_of_arm hFG hFreach hadj

/--
[bc103_deg3_of_noBypass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc103contractdeg.lean)
-/
@[path]
private lemma bc103_deg3_of_noBypass_eq
  {d : ℕ}
  [Fintype V]
  {G F : SimpleGraph V}
  [DecidableRel F.Adj]
  {u v₁ v₂ v₃ : V}
-- given
  (hFG : F ≤ G)
  (hFreach : ∀ a b, G.Reachable a b → F.Reachable a b)
  (hadj₁ : G.Adj u v₁)
  (hadj₂ : G.Adj u v₂)
  (hadj₃ : G.Adj u v₃)
  (hcut₁₂ : ¬ (G.deleteIncidenceSet u).Reachable v₁ v₂)
  (hcut₁₃ : ¬ (G.deleteIncidenceSet u).Reachable v₁ v₃)
  (hcut₂₃ : ¬ (G.deleteIncidenceSet u).Reachable v₂ v₃) :
-- imply
  3 ≤ F.degree u := by
-- proof
  apply StatMech.Walls.bc103_deg3_of_noBypass hFG hFreach hadj₁ hadj₂ hadj₃ hcut₁₂ hcut₁₃ hcut₂₃

/--
[bc103_deg3_spanForest_of_noBypass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc103contractdeg.lean)
-/
@[path]
private lemma bc103_deg3_spanForest_of_noBypass_eq
  {d : ℕ}
  [Fintype V]
  {G : SimpleGraph V}
  [DecidableRel (osf_spanForest G).Adj]
  {u v₁ v₂ v₃ : V}
-- given
  (hadj₁ : G.Adj u v₁)
  (hadj₂ : G.Adj u v₂)
  (hadj₃ : G.Adj u v₃)
  (hcut₁₂ : ¬ (G.deleteIncidenceSet u).Reachable v₁ v₂)
  (hcut₁₃ : ¬ (G.deleteIncidenceSet u).Reachable v₁ v₃)
  (hcut₂₃ : ¬ (G.deleteIncidenceSet u).Reachable v₂ v₃) :
-- imply
  3 ≤ (osf_spanForest G).degree u := by
-- proof
  apply StatMech.Walls.bc103_deg3_spanForest_of_noBypass G hadj₁ hadj₂ hadj₃ hcut₁₂ hcut₁₃ hcut₂₃

/--
[bc103_arms_distinct_of_deleteVert_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc103contractdeg.lean)
-/
@[path]
private lemma bc103_arms_distinct_of_deleteVert_cut_eq
  {d : ℕ}
  {G : SimpleGraph V}
  {u v₁ v₂ v₃ : V}
-- given
  (hcut₁₂ : ¬ (G.deleteIncidenceSet u).Reachable v₁ v₂)
  (hcut₁₃ : ¬ (G.deleteIncidenceSet u).Reachable v₁ v₃)
  (hcut₂₃ : ¬ (G.deleteIncidenceSet u).Reachable v₂ v₃) :
-- imply
  v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₃ := by
-- proof
  apply StatMech.Walls.bc103_arms_distinct_of_deleteVert_cut hcut₁₂ hcut₁₃ hcut₂₃

/--
[bc103_globalForest_of_contractedGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc103contractdeg.lean)
-/
@[path]
private lemma bc103_globalForest_of_contractedGraph_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc103_ContractedTrifGraph ω L R) :
-- imply
  bc69_Gn_globalForest ω L R := by
-- proof
  apply StatMech.Walls.bc103_globalForest_of_contractedGraph ω L R h

/--
[bc103_count_of_contractedGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc103contractdeg.lean)
-/
@[path]
private lemma bc103_count_of_contractedGraph_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc103_ContractedTrifGraph ω L R) :
-- imply
  bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc103_count_of_contractedGraph ω L R h

/--
[bc103_infiniteClusters_top_null_of_contractedGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc103contractdeg.lean)
-/
@[path]
private lemma bc103_infiniteClusters_top_null_of_contractedGraph_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (hfe : HasFiniteEnergyMerge μ)
  (hCon : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc103_ContractedTrifGraph ω L R)
  (hcoarseRoute : 0 < μ {ω | numInfiniteClusters d ω = ⊤} → ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d, 0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
-- imply
  μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bc103_infiniteClusters_top_null_of_contractedGraph μ hd hinv hfe L hCon hcoarseRoute

/--
[bc103_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc103contractdeg.lean)
-/
@[path]
private lemma bc103_status_eq
  {d : ℕ} :
-- imply
  (∀ {V : Type} [Fintype V] (G F : SimpleGraph V) [DecidableRel F.Adj], F ≤ G → (∀ a b, G.Reachable a b → F.Reachable a b) → ∀ (u v₁ v₂ v₃ : V), G.Adj u v₁ → G.Adj u v₂ → G.Adj u v₃ → ¬ (G.deleteIncidenceSet u).Reachable v₁ v₂ → ¬ (G.deleteIncidenceSet u).Reachable v₁ v₃ → ¬ (G.deleteIncidenceSet u).Reachable v₂ v₃ → 3 ≤ F.degree u) ∧ (∀ {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel (osf_spanForest G).Adj] (u v₁ v₂ v₃ : V), G.Adj u v₁ → G.Adj u v₂ → G.Adj u v₃ → ¬ (G.deleteIncidenceSet u).Reachable v₁ v₂ → ¬ (G.deleteIncidenceSet u).Reachable v₁ v₃ → ¬ (G.deleteIncidenceSet u).Reachable v₂ v₃ → 3 ≤ (osf_spanForest G).degree u) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), bc103_ContractedTrifGraph ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) := by
-- proof
  apply StatMech.Walls.bc103_status


-- created on 2026-10-23
