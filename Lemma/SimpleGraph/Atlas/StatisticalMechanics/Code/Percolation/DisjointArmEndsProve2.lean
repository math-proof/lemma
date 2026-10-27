import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve2.Part3
open Set SimpleGraph Finset MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[daep2_armEnds_share_forces_branch_connection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsProve2.lean)
-/
@[path]
private lemma daep2_armEnds_share_forces_branch_connection_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x a b w : Site d}
-- given
  (hwa : Connected d (removeSite x ω) a w)
  (hwb : Connected d (removeSite x ω) b w) :
-- imply
  Connected d (removeSite x ω) a b := by
-- proof
  apply StatMech.Percolation.daep2_armEnds_share_forces_branch_connection ω hwa hwb

/--
[daep2_no_shared_boundary_of_disconnected_branches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsProve2.lean)
-/
@[path]
private lemma daep2_no_shared_boundary_of_disconnected_branches_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x a b : Site d}
-- given
  (hdis : ¬ Connected d (removeSite x ω) a b) :
-- imply
  ∀ w, ¬ (Connected d (removeSite x ω) a w ∧ Connected d (removeSite x ω) b w) := by
-- proof
  apply StatMech.Percolation.daep2_no_shared_boundary_of_disconnected_branches ω hdis

/--
[daep2_globalCut_disconnected_of_omega_disconnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsProve2.lean)
-/
@[path]
private lemma daep2_globalCut_disconnected_of_omega_disconnected_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
  {u v : Site d}
-- given
  (hdis : ¬ Connected d ω u v) :
-- imply
  ¬ Connected d (removeSites T ω) u v := by
-- proof
  apply StatMech.Percolation.daep2_globalCut_disconnected_of_omega_disconnected T ω hdis

/--
[daep2_crossCluster_branches_globalCut_disconnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsProve2.lean)
-/
@[path]
private lemma daep2_crossCluster_branches_globalCut_disconnected_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y a b : Site d}
-- given
  (hxa : Connected d ω x a)
  (hyb : Connected d ω y b)
  (hxy : ¬ Connected d ω x y) :
-- imply
  ¬ Connected d (removeSites T ω) a b := by
-- proof
  apply StatMech.Percolation.daep2_crossCluster_branches_globalCut_disconnected T ω hxa hyb hxy

/--
[daep2_removeSites_le_removeSite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsProve2.lean)
-/
@[path]
private lemma daep2_removeSites_le_removeSite_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (hxT : x ∈ T) :
-- imply
  removeSites T ω ≤ removeSite x ω := by
-- proof
  apply StatMech.Percolation.daep2_removeSites_le_removeSite T ω hxT

/--
[daep2_globalCut_disconnected_of_singleCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsProve2.lean)
-/
@[path]
private lemma daep2_globalCut_disconnected_of_singleCut_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x u v : Site d}
-- given
  (hxT : x ∈ T)
  (hdis : ¬ Connected d (removeSite x ω) u v) :
-- imply
  ¬ Connected d (removeSites T ω) u v := by
-- proof
  apply StatMech.Percolation.daep2_globalCut_disconnected_of_singleCut T ω hxT hdis

/--
[daep2_globalCutSeparation_of_sameCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsProve2.lean)
-/
@[path]
private lemma daep2_globalCutSeparation_of_sameCluster_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : daep2_SameClusterCutSeparation ω n) :
-- imply
  daep_GlobalCutSeparation ω n := by
-- proof
  apply StatMech.Percolation.daep2_globalCutSeparation_of_sameCluster ω n h

/--
[daep2_meets_at_most_one_branch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsProve2.lean)
-/
@[path]
private lemma daep2_meets_at_most_one_branch_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x a₁ a₂ a₃ : Site d}
  {v : Site d}
-- given
  (hd12 : ¬ Connected d (removeSite x ω) a₁ a₂)
  (hd13 : ¬ Connected d (removeSite x ω) a₁ a₃)
  (hd23 : ¬ Connected d (removeSite x ω) a₂ a₃) :
-- imply
  ¬ (Connected d (removeSite x ω) a₁ v ∧ Connected d (removeSite x ω) a₂ v) ∧ ¬ (Connected d (removeSite x ω) a₁ v ∧ Connected d (removeSite x ω) a₃ v) ∧ ¬ (Connected d (removeSite x ω) a₂ v ∧ Connected d (removeSite x ω) a₃ v) := by
-- proof
  apply StatMech.Percolation.daep2_meets_at_most_one_branch ω hd12 hd13 hd23 v

/--
[daep2_two_branches_avoid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsProve2.lean)
-/
@[path]
private lemma daep2_two_branches_avoid_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x a₁ a₂ a₃ : Site d}
  {v : Site d}
-- given
  (hd12 : ¬ Connected d (removeSite x ω) a₁ a₂)
  (hd13 : ¬ Connected d (removeSite x ω) a₁ a₃)
  (hd23 : ¬ Connected d (removeSite x ω) a₂ a₃) :
-- imply
  (¬ Connected d (removeSite x ω) a₁ v ∧ ¬ Connected d (removeSite x ω) a₂ v) ∨ (¬ Connected d (removeSite x ω) a₁ v ∧ ¬ Connected d (removeSite x ω) a₃ v) ∨ (¬ Connected d (removeSite x ω) a₂ v ∧ ¬ Connected d (removeSite x ω) a₃ v) := by
-- proof
  apply StatMech.Percolation.daep2_two_branches_avoid ω hd12 hd13 hd23 v

/--
[daep2_sameClusterCutSeparation_of_singleCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsProve2.lean)
-/
@[path]
private lemma daep2_sameClusterCutSeparation_of_singleCut_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : daep2_SingleCutBranchSeparation ω n) :
-- imply
  daep2_SameClusterCutSeparation ω n := by
-- proof
  apply StatMech.Percolation.daep2_sameClusterCutSeparation_of_singleCut ω n h

/--
[daep2_sameClusterCutSeparation_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsProve2.lean)
-/
@[path]
private lemma daep2_sameClusterCutSeparation_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  daep2_SameClusterCutSeparation ω n := by
-- proof
  apply StatMech.Percolation.daep2_sameClusterCutSeparation_of_noTrif ω n hno

/--
[daep2_sameClusterCutSeparation_of_uniqueTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsProve2.lean)
-/
@[path]
private lemma daep2_sameClusterCutSeparation_of_uniqueTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ a : Site d}
-- given
  (hx0box : x₀ ∈ box d n)
  (htri0 : IsTrifurcation d ω x₀)
  (habox : a ∈ box d n)
  (haconn : Connected d ω x₀ a)
  (hainf : (cluster d (removeSite x₀ ω) a).Infinite)
  (huniq : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀) :
-- imply
  daep2_SameClusterCutSeparation ω n := by
-- proof
  apply StatMech.Percolation.daep2_sameClusterCutSeparation_of_uniqueTrif ω n hx0box htri0 habox haconn hainf huniq

/--
[daep2_singleCutBranchSeparation_of_distinctClusters](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsProve2.lean)
-/
@[path]
private lemma daep2_singleCutBranchSeparation_of_distinctClusters_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {b : Site d → Site d}
-- given
  (hb : ∀ x, x ∈ box d n → IsTrifurcation d ω x → b x ∈ box d n ∧ Connected d ω x (b x) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite)
  (hsep : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y → x ≠ y → ¬ Connected d ω x y) :
-- imply
  daep2_SingleCutBranchSeparation ω n := by
-- proof
  apply StatMech.Percolation.daep2_singleCutBranchSeparation_of_distinctClusters ω n b hb hsep

/--
[daep2_singleCutBranchSeparation_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsProve2.lean)
-/
@[path]
private lemma daep2_singleCutBranchSeparation_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  daep2_SingleCutBranchSeparation ω n := by
-- proof
  apply StatMech.Percolation.daep2_singleCutBranchSeparation_of_noTrif ω n hno

/--
[daep2_Tcount_le_boundary_of_sameCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsProve2.lean)
-/
@[path]
private lemma daep2_Tcount_le_boundary_of_sameCluster_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (h : daep2_SameClusterCutSeparation ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.daep2_Tcount_le_boundary_of_sameCluster ω n hn h

/--
[daep2_burton_keane_bernoulli_of_sameCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsProve2.lean)
-/
@[path]
private lemma daep2_burton_keane_bernoulli_of_sameCluster_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → daep2_SameClusterCutSeparation ω n)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Percolation.daep2_burton_keane_bernoulli_of_sameCluster hd p hp1 hp0 hres htrif

/--
[daep2_Tcount_le_boundary_of_singleCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsProve2.lean)
-/
@[path]
private lemma daep2_Tcount_le_boundary_of_singleCut_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (h : daep2_SingleCutBranchSeparation ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.daep2_Tcount_le_boundary_of_singleCut ω n hn h

/--
[daep2_burton_keane_bernoulli_of_singleCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsProve2.lean)
-/
@[path]
private lemma daep2_burton_keane_bernoulli_of_singleCut_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → daep2_SingleCutBranchSeparation ω n)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Percolation.daep2_burton_keane_bernoulli_of_singleCut hd p hp1 hp0 hres htrif


-- created on 2026-10-23
