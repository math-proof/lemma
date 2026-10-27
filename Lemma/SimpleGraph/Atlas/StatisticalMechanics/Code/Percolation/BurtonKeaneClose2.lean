import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose2.Part3
open Set SimpleGraph Finset MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[bk2_card_le_of_pairwiseDisjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneClose2.lean)
-/
@[path]
private lemma bk2_card_le_of_pairwiseDisjoint_eq
  {d : ℕ}
  [DecidableEq β]
  {S : Finset α}
  {T : Finset β}
  {A : α → Finset β}
-- given
  (hne : ∀ x ∈ S, (A x).Nonempty)
  (hsub : ∀ x ∈ S, A x ⊆ T)
  (hdisj : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Disjoint (A x) (A y)) :
-- imply
  S.card ≤ T.card := by
-- proof
  apply StatMech.Percolation.bk2_card_le_of_pairwiseDisjoint S T A hne hsub hdisj

/--
[bk2_mem_armEndFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneClose2.lean)
-/
@[path]
private lemma bk2_mem_armEndFinset_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x z : Site d} :
-- imply
  z ∈ bk2_armEndFinset ω n x ↔ z ∈ vertexBoundary d n ∧ Connected d ω x z := by
-- proof
  apply StatMech.Percolation.bk2_mem_armEndFinset

/--
[bk2_armEndFinset_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneClose2.lean)
-/
@[path]
private lemma bk2_armEndFinset_subset_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x : Site d} :
-- imply
  bk2_armEndFinset ω n x ⊆ tfc_boundaryFinset d n := by
-- proof
  apply StatMech.Percolation.bk2_armEndFinset_subset ω n x

/--
[bk2_armEndFinset_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneClose2.lean)
-/
@[path]
private lemma bk2_armEndFinset_nonempty_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x : Site d}
-- given
  (hn : 1 ≤ n)
  (hxbox : x ∈ box d n)
  (htri : IsTrifurcation d ω x) :
-- imply
  (bk2_armEndFinset ω n x).Nonempty := by
-- proof
  apply StatMech.Percolation.bk2_armEndFinset_nonempty ω n hn x hxbox htri

/--
[bk2_distinctArmEnds_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneClose2.lean)
-/
@[path]
private lemma bk2_distinctArmEnds_of_disjoint_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (hdisj : bk2_DisjointArmEnds ω n) :
-- imply
  tfc_DistinctArmEnds ω n := by
-- proof
  apply StatMech.Percolation.bk2_distinctArmEnds_of_disjoint ω n hn hdisj

/--
[bk2_Tcount_le_boundary_of_disjointArmEnds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneClose2.lean)
-/
@[path]
private lemma bk2_Tcount_le_boundary_of_disjointArmEnds_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (hdisj : bk2_DisjointArmEnds ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.bk2_Tcount_le_boundary_of_disjointArmEnds ω n hn hdisj

/--
[bk2_Tcount_le_boundary_direct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneClose2.lean)
-/
@[path]
private lemma bk2_Tcount_le_boundary_direct_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (hdisj : bk2_DisjointArmEnds ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.bk2_Tcount_le_boundary_direct ω n hn hdisj

/--
[bk2_disjointArmEnds_of_subsingleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneClose2.lean)
-/
@[path]
private lemma bk2_disjointArmEnds_of_subsingleton_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hsub : ∀ x y, x ∈ box d n → IsTrifurcation d ω x → y ∈ box d n → IsTrifurcation d ω y → x = y) :
-- imply
  bk2_DisjointArmEnds ω n := by
-- proof
  apply StatMech.Percolation.bk2_disjointArmEnds_of_subsingleton ω n hsub

/--
[bk2_branch_reaches_boundary_rem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneClose2.lean)
-/
@[path]
private lemma bk2_branch_reaches_boundary_rem_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x a : Site d}
-- given
  (hn : 1 ≤ n)
  (habox : a ∈ box d n)
  (hinf : (cluster d (removeSite x ω) a).Infinite) :
-- imply
  ∃ z ∈ vertexBoundary d n, Connected d (removeSite x ω) a z := by
-- proof
  apply StatMech.Percolation.bk2_branch_reaches_boundary_rem ω n hn x a habox hinf

/--
[bk2_armEnds_disconnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneClose2.lean)
-/
@[path]
private lemma bk2_armEnds_disconnected_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x a₁ a₂ z₁ z₂ : Site d}
-- given
  (hz1 : Connected d (removeSite x ω) a₁ z₁)
  (hz2 : Connected d (removeSite x ω) a₂ z₂)
  (hdis : ¬ Connected d (removeSite x ω) a₁ a₂) :
-- imply
  ¬ Connected d (removeSite x ω) z₁ z₂ := by
-- proof
  apply StatMech.Percolation.bk2_armEnds_disconnected ω hz1 hz2 hdis

/--
[bk2_armEnds_distinct_of_disconnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneClose2.lean)
-/
@[path]
private lemma bk2_armEnds_distinct_of_disconnected_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x z₁ z₂ : Site d}
-- given
  (hdis : ¬ Connected d (removeSite x ω) z₁ z₂) :
-- imply
  z₁ ≠ z₂ := by
-- proof
  apply StatMech.Percolation.bk2_armEnds_distinct_of_disconnected ω hdis

/--
[bk2_trif_three_disjoint_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneClose2.lean)
-/
@[path]
private lemma bk2_trif_three_disjoint_boundary_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x a₁ a₂ a₃ : Site d}
-- given
  (hn : 1 ≤ n)
  (ha1box : a₁ ∈ box d n)
  (ha2box : a₂ ∈ box d n)
  (ha3box : a₃ ∈ box d n)
  (hi1 : (cluster d (removeSite x ω) a₁).Infinite)
  (hi2 : (cluster d (removeSite x ω) a₂).Infinite)
  (hi3 : (cluster d (removeSite x ω) a₃).Infinite)
  (hd12 : ¬ Connected d (removeSite x ω) a₁ a₂)
  (hd13 : ¬ Connected d (removeSite x ω) a₁ a₃)
  (hd23 : ¬ Connected d (removeSite x ω) a₂ a₃) :
-- imply
  ∃ z₁ z₂ z₃ : Site d, (z₁ ∈ vertexBoundary d n ∧ z₂ ∈ vertexBoundary d n ∧ z₃ ∈ vertexBoundary d n) ∧ (Connected d (removeSite x ω) a₁ z₁ ∧ Connected d (removeSite x ω) a₂ z₂ ∧ Connected d (removeSite x ω) a₃ z₃) ∧ (¬ Connected d (removeSite x ω) z₁ z₂ ∧ ¬ Connected d (removeSite x ω) z₁ z₃ ∧ ¬ Connected d (removeSite x ω) z₂ z₃) ∧ (z₁ ≠ z₂ ∧ z₁ ≠ z₃ ∧ z₂ ≠ z₃) := by
-- proof
  apply StatMech.Percolation.bk2_trif_three_disjoint_boundary ω n hn ha1box ha2box ha3box hi1 hi2 hi3 hd12 hd13 hd23

/--
[bk2_burton_keane_bernoulli](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneClose2.lean)
-/
@[path]
private lemma bk2_burton_keane_bernoulli_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hdisj : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bk2_DisjointArmEnds ω n)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Percolation.bk2_burton_keane_bernoulli hd p hp1 hp0 hdisj htrif


-- created on 2026-10-23
