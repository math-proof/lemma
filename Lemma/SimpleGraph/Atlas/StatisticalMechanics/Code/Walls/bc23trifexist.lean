import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bc23trifexist
open Set SimpleGraph MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech.Percolation.DisjointPaths StatMech StatMech.Walls


/--
[bc23_corridor_of_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc23trifexist.lean)
-/
@[path]
private lemma bc23_corridor_of_walk_eq
  {d : ℕ}
  {G : Finset (Sym2 (Site d))}
  {a b : Site d}
  {w : (hypercubicLattice d).Walk a b}
-- given
  (hedges : ∀ e ∈ w.edges, e ∈ G)
  (h0 : (0 : Site d) ∉ w.support) :
-- imply
  Relation.ReflTransGen (CorridorStep G) a b := by
-- proof
  apply StatMech.Walls.bc23_corridor_of_walk G w hedges h0

/--
[bc23_mem_walkEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc23trifexist.lean)
-/
@[path]
private lemma bc23_mem_walkEdges_eq
  {d : ℕ}
  {a b : Site d}
  {w : (hypercubicLattice d).Walk a b}
  {e : Sym2 (Site d)}
-- given
  (he : e ∈ w.edges) :
-- imply
  e ∈ bc23_walkEdges w := by
-- proof
  apply StatMech.Walls.bc23_mem_walkEdges w he

/--
[bc23_corridor_of_walk_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc23trifexist.lean)
-/
@[path]
private lemma bc23_corridor_of_walk_subset_eq
  {d : ℕ}
  {G : Finset (Sym2 (Site d))}
  {a b : Site d}
  {w : (hypercubicLattice d).Walk a b}
-- given
  (hsub : bc23_walkEdges w ⊆ G)
  (h0 : (0 : Site d) ∉ w.support) :
-- imply
  Relation.ReflTransGen (CorridorStep G) a b := by
-- proof
  apply StatMech.Walls.bc23_corridor_of_walk_subset G w hsub h0

/--
[bc23_mengerCore_of_corridors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc23trifexist.lean)
-/
@[path]
private lemma bc23_mengerCore_of_corridors_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a₁ a₂ a₃ : Site d}
  {G : Finset (Sym2 (Site d))}
  {w₁ w₂ w₃ : Site d}
-- given
  (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
  (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧ (hypercubicLattice d).Adj 0 a₃)
  (hcor : Relation.ReflTransGen (CorridorStep G) a₁ w₁ ∧ Relation.ReflTransGen (CorridorStep G) a₂ w₂ ∧ Relation.ReflTransGen (CorridorStep G) a₃ w₃)
  (hinf : (cluster d (removeSite 0 (forceOpenFinset G ω)) w₁).Infinite ∧ (cluster d (removeSite 0 (forceOpenFinset G ω)) w₂).Infinite ∧ (cluster d (removeSite 0 (forceOpenFinset G ω)) w₃).Infinite)
  (hdist : cluster d (removeSite 0 (forceOpenFinset G ω)) w₁ ≠ cluster d (removeSite 0 (forceOpenFinset G ω)) w₂ ∧ cluster d (removeSite 0 (forceOpenFinset G ω)) w₁ ≠ cluster d (removeSite 0 (forceOpenFinset G ω)) w₃ ∧ cluster d (removeSite 0 (forceOpenFinset G ω)) w₂ ≠ cluster d (removeSite 0 (forceOpenFinset G ω)) w₃) :
-- imply
  MengerCore ω := by
-- proof
  apply StatMech.Walls.bc23_mengerCore_of_corridors ω a₁ a₂ a₃ G w₁ w₂ w₃ hne hadj hcor hinf hdist

/--
[bc23_removeSite_le_forceOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc23trifexist.lean)
-/
@[path]
private lemma bc23_removeSite_le_forceOpen_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {G : Finset (Sym2 (Site d))} :
-- imply
  removeSite 0 ω ≤ removeSite 0 (forceOpenFinset G ω) := by
-- proof
  apply StatMech.Walls.bc23_removeSite_le_forceOpen ω G

/--
[bc23_forcedCluster_infinite_of_originFree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc23trifexist.lean)
-/
@[path]
private lemma bc23_forcedCluster_infinite_of_originFree_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {G : Finset (Sym2 (Site d))}
  {b : Site d}
-- given
  (h0 : (0 : Site d) ∉ cluster d ω b)
  (hinf : (cluster d ω b).Infinite) :
-- imply
  (cluster d (removeSite 0 (forceOpenFinset G ω)) b).Infinite := by
-- proof
  apply StatMech.Walls.bc23_forcedCluster_infinite_of_originFree ω G b h0 hinf

/--
[bc23_mengerCore_of_latticeCorridors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc23trifexist.lean)
-/
@[path]
private lemma bc23_mengerCore_of_latticeCorridors_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a₁ a₂ a₃ b₁ b₂ b₃ : Site d}
  {w₁ : (hypercubicLattice d).Walk a₁ b₁}
  {w₂ : (hypercubicLattice d).Walk a₂ b₂}
  {w₃ : (hypercubicLattice d).Walk a₃ b₃}
  {S₁ S₂ S₃ : Set (Site d)}
-- given
  (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
  (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧ (hypercubicLattice d).Adj 0 a₃)
  (hw0₁ : (0 : Site d) ∉ w₁.support)
  (hw0₂ : (0 : Site d) ∉ w₂.support)
  (hw0₃ : (0 : Site d) ∉ w₃.support)
  (h0 : (0 : Site d) ∉ cluster d ω b₁ ∧ (0 : Site d) ∉ cluster d ω b₂ ∧ (0 : Site d) ∉ cluster d ω b₃)
  (hinf : (cluster d ω b₁).Infinite ∧ (cluster d ω b₂).Infinite ∧ (cluster d ω b₃).Infinite)
  (hb₁ : b₁ ∈ S₁)
  (hb₂ : b₂ ∈ S₂)
  (hb₃ : b₃ ∈ S₃)
  (hcl₁ : ∀ u v, u ∈ S₁ → (openSubgraph d (removeSite 0 (forceOpenFinset (bc23_walkEdges w₁ ∪ bc23_walkEdges w₂ ∪ bc23_walkEdges w₃) ω))).Adj u v → v ∈ S₁)
  (hcl₂ : ∀ u v, u ∈ S₂ → (openSubgraph d (removeSite 0 (forceOpenFinset (bc23_walkEdges w₁ ∪ bc23_walkEdges w₂ ∪ bc23_walkEdges w₃) ω))).Adj u v → v ∈ S₂)
  (hcl₃ : ∀ u v, u ∈ S₃ → (openSubgraph d (removeSite 0 (forceOpenFinset (bc23_walkEdges w₁ ∪ bc23_walkEdges w₂ ∪ bc23_walkEdges w₃) ω))).Adj u v → v ∈ S₃)
  (hd12 : Disjoint S₁ S₂)
  (hd13 : Disjoint S₁ S₃)
  (hd23 : Disjoint S₂ S₃) :
-- imply
  MengerCore ω := by
-- proof
  apply StatMech.Walls.bc23_mengerCore_of_latticeCorridors ω a₁ a₂ a₃ b₁ b₂ b₃ w₁ w₂ w₃ hne hadj hw0₁ hw0₂ hw0₃ h0 hinf S₁ S₂ S₃ hb₁ hb₂ hb₃ hcl₁ hcl₂ hcl₃ hd12 hd13 hd23

/--
[bc23_mengerRoutingCover_of_latticeCorridorRouting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc23trifexist.lean)
-/
@[path]
private lemma bc23_mengerRoutingCover_of_latticeCorridorRouting_eq
  {d : ℕ}
  {d n : ℕ}
-- given
  (h : bc23_LatticeCorridorRouting d n) :
-- imply
  MengerRoutingCover d n := by
-- proof
  apply StatMech.Walls.bc23_mengerRoutingCover_of_latticeCorridorRouting d n h

/--
[bc23_burtonKeane_uniqueness_of_latticeCorridorRouting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc23trifexist.lean)
-/
@[path]
private lemma bc23_burtonKeane_uniqueness_of_latticeCorridorRouting_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {bdry : ℕ → ℕ}
-- given
  (herg : IsErgodic (G := Multiplicative (Site d)) μ)
  (hfe : HasFiniteEnergyMerge μ)
  (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
  (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
  (hdens : Filter.Tendsto (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ)) Filter.atTop (nhds 0))
  (hr : ∀ n : ℕ, bc23_LatticeCorridorRouting d n) :
-- imply
  (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1) ∧ μ (atLeastTwoInfinite d) = 0 ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc23_burtonKeane_uniqueness_of_latticeCorridorRouting μ herg hfe bdry hbound hvol hdens hr

/--
[bc23_nil_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc23trifexist.lean)
-/
@[path]
private lemma bc23_nil_support_eq
  {d : ℕ}
  {a : Site d} :
-- imply
  ((Walk.nil : (hypercubicLattice d).Walk a a)).support = [a] := by
-- proof
  apply StatMech.Walls.bc23_nil_support a

/--
[bc23_mengerCore_of_originFree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc23trifexist.lean)
-/
@[path]
private lemma bc23_mengerCore_of_originFree_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a₁ a₂ a₃ : Site d}
-- given
  (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
  (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧ (hypercubicLattice d).Adj 0 a₃)
  (h0 : (0 : Site d) ∉ cluster d ω a₁ ∧ (0 : Site d) ∉ cluster d ω a₂ ∧ (0 : Site d) ∉ cluster d ω a₃)
  (hinf : (cluster d ω a₁).Infinite ∧ (cluster d ω a₂).Infinite ∧ (cluster d ω a₃).Infinite)
  (hdist : cluster d ω a₁ ≠ cluster d ω a₂ ∧ cluster d ω a₁ ≠ cluster d ω a₃ ∧ cluster d ω a₂ ≠ cluster d ω a₃) :
-- imply
  MengerCore ω := by
-- proof
  apply StatMech.Walls.bc23_mengerCore_of_originFree ω a₁ a₂ a₃ hne hadj h0 hinf hdist


-- created on 2026-10-23
