import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve
open Set SimpleGraph Finset MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[daep_mem_cutArmEnds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsProve.lean)
-/
@[path]
private lemma daep_mem_cutArmEnds_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x a z : Site d} :
-- imply
  z ∈ daep_cutArmEnds ω n x a ↔ z ∈ vertexBoundary d n ∧ Connected d (removeSite x ω) a z := by
-- proof
  apply StatMech.Percolation.daep_mem_cutArmEnds

/--
[daep_cutArmEnds_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsProve.lean)
-/
@[path]
private lemma daep_cutArmEnds_subset_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x a : Site d} :
-- imply
  daep_cutArmEnds ω n x a ⊆ tfc_boundaryFinset d n := by
-- proof
  apply StatMech.Percolation.daep_cutArmEnds_subset ω n x a

/--
[daep_cutArmEnds_disjoint_of_disconnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsProve.lean)
-/
@[path]
private lemma daep_cutArmEnds_disjoint_of_disconnected_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x a₁ a₂ : Site d}
-- given
  (hdis : ¬ Connected d (removeSite x ω) a₁ a₂) :
-- imply
  Disjoint (daep_cutArmEnds ω n x a₁) (daep_cutArmEnds ω n x a₂) := by
-- proof
  apply StatMech.Percolation.daep_cutArmEnds_disjoint_of_disconnected ω n hdis

/--
[daep_cutArmEnds_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsProve.lean)
-/
@[path]
private lemma daep_cutArmEnds_nonempty_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x a : Site d}
-- given
  (hn : 1 ≤ n)
  (habox : a ∈ box d n)
  (hinf : (cluster d (removeSite x ω) a).Infinite) :
-- imply
  (daep_cutArmEnds ω n x a).Nonempty := by
-- proof
  apply StatMech.Percolation.daep_cutArmEnds_nonempty ω n hn x a habox hinf

/--
[daep_three_cut_blocks_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsProve.lean)
-/
@[path]
private lemma daep_three_cut_blocks_disjoint_eq
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
  ((daep_cutArmEnds ω n x a₁).Nonempty ∧ (daep_cutArmEnds ω n x a₂).Nonempty ∧ (daep_cutArmEnds ω n x a₃).Nonempty) ∧ (daep_cutArmEnds ω n x a₁ ⊆ tfc_boundaryFinset d n ∧ daep_cutArmEnds ω n x a₂ ⊆ tfc_boundaryFinset d n ∧ daep_cutArmEnds ω n x a₃ ⊆ tfc_boundaryFinset d n) ∧ (Disjoint (daep_cutArmEnds ω n x a₁) (daep_cutArmEnds ω n x a₂) ∧ Disjoint (daep_cutArmEnds ω n x a₁) (daep_cutArmEnds ω n x a₃) ∧ Disjoint (daep_cutArmEnds ω n x a₂) (daep_cutArmEnds ω n x a₃)) := by
-- proof
  apply StatMech.Percolation.daep_three_cut_blocks_disjoint ω n hn ha1box ha2box ha3box hi1 hi2 hi3 hd12 hd13 hd23

/--
[daep_doubleCut_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsProve.lean)
-/
@[path]
private lemma daep_doubleCut_le_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : Site d} :
-- imply
  removeSite x (removeSite y ω) ≤ ω := by
-- proof
  apply StatMech.Percolation.daep_doubleCut_le ω x y

/--
[daep_doubleCut_arms_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsProve.lean)
-/
@[path]
private lemma daep_doubleCut_arms_disjoint_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x y a b : Site d}
-- given
  (hdis : ¬ Connected d (removeSite x (removeSite y ω)) a b) :
-- imply
  Disjoint (daep_cutArmEnds (removeSite y ω) n x a) (daep_cutArmEnds (removeSite x ω) n y b) := by
-- proof
  apply StatMech.Percolation.daep_doubleCut_arms_disjoint ω n hdis

/--
[daep_distinctArmEnds_of_cutDisjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsProve.lean)
-/
@[path]
private lemma daep_distinctArmEnds_of_cutDisjoint_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : daep_CutDisjointArmEnds ω n) :
-- imply
  tfc_DistinctArmEnds ω n := by
-- proof
  apply StatMech.Percolation.daep_distinctArmEnds_of_cutDisjoint ω n h

/--
[daep_Tcount_le_boundary_of_cutDisjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsProve.lean)
-/
@[path]
private lemma daep_Tcount_le_boundary_of_cutDisjoint_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : daep_CutDisjointArmEnds ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.daep_Tcount_le_boundary_of_cutDisjoint ω n h

/--
[daep_cutDisjoint_of_subsingleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsProve.lean)
-/
@[path]
private lemma daep_cutDisjoint_of_subsingleton_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (hsub : ∀ x y, x ∈ box d n → IsTrifurcation d ω x → y ∈ box d n → IsTrifurcation d ω y → x = y) :
-- imply
  daep_CutDisjointArmEnds ω n := by
-- proof
  apply StatMech.Percolation.daep_cutDisjoint_of_subsingleton ω n hn hsub

/--
[daep_cutDisjoint_of_disjointArmEnds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsProve.lean)
-/
@[path]
private lemma daep_cutDisjoint_of_disjointArmEnds_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (hdisj : bk2_DisjointArmEnds ω n) :
-- imply
  daep_CutDisjointArmEnds ω n := by
-- proof
  apply StatMech.Percolation.daep_cutDisjoint_of_disjointArmEnds ω n hn hdisj

/--
[daep_burton_keane_bernoulli](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsProve.lean)
-/
@[path]
private lemma daep_burton_keane_bernoulli_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → daep_CutDisjointArmEnds ω n)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Percolation.daep_burton_keane_bernoulli hd p hp1 hp0 hres htrif

/--
[daep_removeSites_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsProve.lean)
-/
@[path]
private lemma daep_removeSites_le_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  removeSites T ω ≤ ω := by
-- proof
  apply StatMech.Percolation.daep_removeSites_le T ω

/--
[daep_mem_globalCutArmEnds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsProve.lean)
-/
@[path]
private lemma daep_mem_globalCutArmEnds_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {a z : Site d} :
-- imply
  z ∈ daep_globalCutArmEnds T ω n a ↔ z ∈ vertexBoundary d n ∧ Connected d (removeSites T ω) a z := by
-- proof
  apply StatMech.Percolation.daep_mem_globalCutArmEnds

/--
[daep_globalCutArmEnds_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsProve.lean)
-/
@[path]
private lemma daep_globalCutArmEnds_connected_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {a z : Site d}
-- given
  (hz : z ∈ daep_globalCutArmEnds T ω n a) :
-- imply
  Connected d ω a z := by
-- proof
  apply StatMech.Percolation.daep_globalCutArmEnds_connected T ω n hz

/--
[daep_globalCutArmEnds_disjoint_of_disconnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsProve.lean)
-/
@[path]
private lemma daep_globalCutArmEnds_disjoint_of_disconnected_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {a₁ a₂ : Site d}
-- given
  (hdis : ¬ Connected d (removeSites T ω) a₁ a₂) :
-- imply
  Disjoint (daep_globalCutArmEnds T ω n a₁) (daep_globalCutArmEnds T ω n a₂) := by
-- proof
  apply StatMech.Percolation.daep_globalCutArmEnds_disjoint_of_disconnected T ω n hdis

/--
[daep_infinite_reaches_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsProve.lean)
-/
@[path]
private lemma daep_infinite_reaches_boundary_eq
  {d : ℕ}
  {ω' : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {a : Site d}
-- given
  (hn : 1 ≤ n)
  (habox : a ∈ box d n)
  (hinf : (cluster d ω' a).Infinite) :
-- imply
  ∃ z ∈ vertexBoundary d n, Connected d ω' a z := by
-- proof
  apply StatMech.Percolation.daep_infinite_reaches_boundary ω' n hn a habox hinf

/--
[daep_globalCutArmEnds_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsProve.lean)
-/
@[path]
private lemma daep_globalCutArmEnds_nonempty_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {a : Site d}
-- given
  (hn : 1 ≤ n)
  (habox : a ∈ box d n)
  (hinf : (cluster d (removeSites T ω) a).Infinite) :
-- imply
  (daep_globalCutArmEnds T ω n a).Nonempty := by
-- proof
  apply StatMech.Percolation.daep_globalCutArmEnds_nonempty T ω n hn a habox hinf

/--
[daep_cutDisjoint_of_globalCutSeparation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsProve.lean)
-/
@[path]
private lemma daep_cutDisjoint_of_globalCutSeparation_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (h : daep_GlobalCutSeparation ω n) :
-- imply
  daep_CutDisjointArmEnds ω n := by
-- proof
  apply StatMech.Percolation.daep_cutDisjoint_of_globalCutSeparation ω n hn h

/--
[daep_removeSites_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsProve.lean)
-/
@[path]
private lemma daep_removeSites_singleton_eq
  {d : ℕ}
  {x : Site d}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  removeSites {x} ω = removeSite x ω := by
-- proof
  apply StatMech.Percolation.daep_removeSites_singleton x ω

/--
[daep_globalCutSeparation_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsProve.lean)
-/
@[path]
private lemma daep_globalCutSeparation_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  daep_GlobalCutSeparation ω n := by
-- proof
  apply StatMech.Percolation.daep_globalCutSeparation_of_noTrif ω n hno

/--
[daep_globalCutSeparation_of_uniqueTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsProve.lean)
-/
@[path]
private lemma daep_globalCutSeparation_of_uniqueTrif_eq
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
  daep_GlobalCutSeparation ω n := by
-- proof
  apply StatMech.Percolation.daep_globalCutSeparation_of_uniqueTrif ω n hx0box htri0 habox haconn hainf huniq

/--
[daep_Tcount_le_boundary_of_globalCutSeparation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsProve.lean)
-/
@[path]
private lemma daep_Tcount_le_boundary_of_globalCutSeparation_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (h : daep_GlobalCutSeparation ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.daep_Tcount_le_boundary_of_globalCutSeparation ω n hn h

/--
[daep_burton_keane_bernoulli_of_globalCutSeparation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsProve.lean)
-/
@[path]
private lemma daep_burton_keane_bernoulli_of_globalCutSeparation_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → daep_GlobalCutSeparation ω n)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Percolation.daep_burton_keane_bernoulli_of_globalCutSeparation hd p hp1 hp0 hres htrif


-- created on 2026-10-23
