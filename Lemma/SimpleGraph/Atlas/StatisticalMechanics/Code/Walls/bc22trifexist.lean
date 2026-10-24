import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bc22trifexist
open StatMech.Lattice StatMech.ConfigSpace SimpleGraph StatMech.Percolation StatMech.Percolation.DisjointPaths StatMech StatMech.Walls


/--
[bc22_through_index_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc22trifexist.lean)
-/
@[path]
private lemma bc22_through_index_unique_eq
  {d : ℕ}
  {V : Type u}
  {GG : SimpleGraph V}
  {A B : Set V}
  {F : bc16_DisjointPathFamily GG A B ι}
  {z₀ : V}
  {i j : ι}
-- given
  (hi : z₀ ∈ (F.p i).support)
  (hj : z₀ ∈ (F.p j).support) :
-- imply
  i = j := by
-- proof
  apply StatMech.Walls.bc22_through_index_unique F z₀ hi hj

/--
[bc22_subfamily_avoiding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc22trifexist.lean)
-/
@[path]
private lemma bc22_subfamily_avoiding_eq
  {d : ℕ}
  {V : Type u}
  {GG : SimpleGraph V}
  {A B : Set V}
  {k : ℕ}
  {F : bc16_DisjointPathFamily GG A B (Fin (k + 1))}
  {z₀ : V} :
-- imply
  ∃ G : bc16_DisjointPathFamily GG A B (Fin k), ∀ i : Fin k, z₀ ∉ (G.p i).support := by
-- proof
  apply StatMech.Walls.bc22_subfamily_avoiding F z₀

/--
[bc22_three_origin_avoiding_boxPaths_of_min4](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc22trifexist.lean)
-/
@[path]
private lemma bc22_three_origin_avoiding_boxPaths_of_min4_eq
  {d : ℕ}
  {V : Type u}
  {GG : SimpleGraph V}
  {d m : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {A B : Set (box d m)}
-- given
  (hmin : ∀ C, bc16_IsSeparator (bc20_boxGraph d m ω) A B C → 4 ≤ C.ncard) :
-- imply
  ∃ G : bc16_DisjointPathFamily (bc20_boxGraph d m ω) A B (Fin 3), ∀ i : Fin 3, bc20_originBox d m ∉ (G.p i).support := by
-- proof
  apply StatMech.Walls.bc22_three_origin_avoiding_boxPaths_of_min4 d m ω hmin

/--
[bc22_connected_removeSite_of_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc22trifexist.lean)
-/
@[path]
private lemma bc22_connected_removeSite_of_path_eq
  {d : ℕ}
  {V : Type u}
  {GG : SimpleGraph V}
  {d m : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {u v : box d m}
  {p : (bc20_boxGraph d m ω).Walk u v}
-- given
  (h0 : bc20_originBox d m ∉ p.support) :
-- imply
  Connected d (removeSite 0 ω) (u : Site d) (v : Site d) := by
-- proof
  apply StatMech.Walls.bc22_connected_removeSite_of_path d m ω p h0

/--
[bc22_branch_origin_cut_survival](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc22trifexist.lean)
-/
@[path]
private lemma bc22_branch_origin_cut_survival_eq
  {d : ℕ}
  {V : Type u}
  {GG : SimpleGraph V}
  {d m : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {A B : Set (box d m)}
-- given
  (hmin : ∀ C, bc16_IsSeparator (bc20_boxGraph d m ω) A B C → 2 ≤ C.ncard) :
-- imply
  ∃ (u v : box d m), u ∈ A ∧ v ∈ B ∧ Connected d (removeSite 0 ω) (u : Site d) (v : Site d) := by
-- proof
  apply StatMech.Walls.bc22_branch_origin_cut_survival d m ω hmin

/--
[bc22_mem_cluster_of_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc22trifexist.lean)
-/
@[path]
private lemma bc22_mem_cluster_of_connected_eq
  {d : ℕ}
  {V : Type u}
  {GG : SimpleGraph V}
  {ϱ : ConfigSpace (Sym2 (Site d))}
  {a u v : Site d}
-- given
  (hu : u ∈ cluster d ϱ a)
  (huv : Connected d ϱ u v) :
-- imply
  v ∈ cluster d ϱ a := by
-- proof
  apply StatMech.Walls.bc22_mem_cluster_of_connected ϱ hu huv

/--
[bc22_mengerCore_of_mergeFree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc22trifexist.lean)
-/
@[path]
private lemma bc22_mengerCore_of_mergeFree_eq
  {d : ℕ}
  {V : Type u}
  {GG : SimpleGraph V}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : bka_MergeFree ω) :
-- imply
  MengerCore ω := by
-- proof
  apply StatMech.Walls.bc22_mengerCore_of_mergeFree ω h

/--
[bc22_mengerRoutingCover_of_boxThreeBranchMinCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc22trifexist.lean)
-/
@[path]
private lemma bc22_mengerRoutingCover_of_boxThreeBranchMinCut_eq
  {d : ℕ}
  {V : Type u}
  {GG : SimpleGraph V}
  {d n : ℕ}
-- given
  (h : bc22_BoxThreeBranchMinCut d n) :
-- imply
  MengerRoutingCover d n := by
-- proof
  apply StatMech.Walls.bc22_mengerRoutingCover_of_boxThreeBranchMinCut d n h

/--
[bc22_burtonKeane_uniqueness_of_boxThreeBranchMinCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc22trifexist.lean)
-/
@[path]
private lemma bc22_burtonKeane_uniqueness_of_boxThreeBranchMinCut_eq
  {d : ℕ}
  {V : Type u}
  {GG : SimpleGraph V}
  {μ : MeasureTheory.Measure (ConfigSpace (Sym2 (Site d)))}
  [MeasureTheory.IsProbabilityMeasure μ]
  {bdry : ℕ → ℕ}
-- given
  (herg : IsErgodic (G := Multiplicative (Site d)) μ)
  (hfe : HasFiniteEnergyMerge μ)
  (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
  (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
  (hdens : Filter.Tendsto (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ)) Filter.atTop (nhds 0))
  (hr : ∀ n : ℕ, bc22_BoxThreeBranchMinCut d n) :
-- imply
  (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1) ∧ μ (atLeastTwoInfinite d) = 0 ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc22_burtonKeane_uniqueness_of_boxThreeBranchMinCut μ herg hfe bdry hbound hvol hdens hr

/--
[bc22_mergeFree_of_threeBranchPaths](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc22trifexist.lean)
-/
@[path]
private lemma bc22_mergeFree_of_threeBranchPaths_eq
  {d : ℕ}
  {V : Type u}
  {GG : SimpleGraph V}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a₁ a₂ a₃ b₁ b₂ b₃ : Site d}
-- given
  (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
  (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧ (hypercubicLattice d).Adj 0 a₃)
  (hconn : Connected d (removeSite 0 ω) a₁ b₁ ∧ Connected d (removeSite 0 ω) a₂ b₂ ∧ Connected d (removeSite 0 ω) a₃ b₃)
  (h0 : (0 : Site d) ∉ cluster d ω b₁ ∧ (0 : Site d) ∉ cluster d ω b₂ ∧ (0 : Site d) ∉ cluster d ω b₃)
  (hinf : (cluster d ω b₁).Infinite ∧ (cluster d ω b₂).Infinite ∧ (cluster d ω b₃).Infinite)
  (hdist : cluster d ω b₁ ≠ cluster d ω b₂ ∧ cluster d ω b₁ ≠ cluster d ω b₃ ∧ cluster d ω b₂ ≠ cluster d ω b₃) :
-- imply
  bka_MergeFree ω := by
-- proof
  apply StatMech.Walls.bc22_mergeFree_of_threeBranchPaths ω a₁ a₂ a₃ b₁ b₂ b₃ hne hadj hconn h0 hinf hdist

/--
[bc22_mergeFree_of_originFree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc22trifexist.lean)
-/
@[path]
private lemma bc22_mergeFree_of_originFree_eq
  {d : ℕ}
  {V : Type u}
  {GG : SimpleGraph V}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a₁ a₂ a₃ : Site d}
-- given
  (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
  (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧ (hypercubicLattice d).Adj 0 a₃)
  (h0 : (0 : Site d) ∉ cluster d ω a₁ ∧ (0 : Site d) ∉ cluster d ω a₂ ∧ (0 : Site d) ∉ cluster d ω a₃)
  (hinf : (cluster d ω a₁).Infinite ∧ (cluster d ω a₂).Infinite ∧ (cluster d ω a₃).Infinite)
  (hdist : cluster d ω a₁ ≠ cluster d ω a₂ ∧ cluster d ω a₁ ≠ cluster d ω a₃ ∧ cluster d ω a₂ ≠ cluster d ω a₃) :
-- imply
  bka_MergeFree ω := by
-- proof
  apply StatMech.Walls.bc22_mergeFree_of_originFree ω a₁ a₂ a₃ hne hadj h0 hinf hdist

/--
[bc22_mengerCore_of_originFree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc22trifexist.lean)
-/
@[path]
private lemma bc22_mengerCore_of_originFree_eq
  {d : ℕ}
  {V : Type u}
  {GG : SimpleGraph V}
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
  apply StatMech.Walls.bc22_mengerCore_of_originFree ω a₁ a₂ a₃ hne hadj h0 hinf hdist

/--
[bc22_subfamily_avoiding_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc22trifexist.lean)
-/
@[path]
private lemma bc22_subfamily_avoiding_nonvacuous_eq
  {d : ℕ}
  {V : Type u}
  {GG : SimpleGraph V}
  {A B : Set V}
  {k : ℕ}
  {F : bc16_DisjointPathFamily GG A B (Fin (k + 1))}
  {z₀ : V} :
-- imply
  ∃ G : bc16_DisjointPathFamily GG A B (Fin k), ∀ i : Fin k, z₀ ∉ (G.p i).support := by
-- proof
  apply StatMech.Walls.bc22_subfamily_avoiding_nonvacuous F z₀

/--
[bc22_mengerCore_of_mergeFree'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc22trifexist.lean)
-/
@[path]
private lemma bc22_mengerCore_of_mergeFree'_eq
  {d : ℕ}
  {V : Type u}
  {GG : SimpleGraph V}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : bka_MergeFree ω) :
-- imply
  MengerCore ω := by
-- proof
  apply StatMech.Walls.bc22_mengerCore_of_mergeFree' ω h


-- created on 2026-10-23
