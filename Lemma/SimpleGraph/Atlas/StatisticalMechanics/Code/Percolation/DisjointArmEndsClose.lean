import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsClose.Part2
open Set SimpleGraph Finset MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[daec_armEnds_eq_of_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsClose.lean)
-/
@[path]
private lemma daec_armEnds_eq_of_connected_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x y : Site d}
-- given
  (hxy : Connected d ω x y) :
-- imply
  bk2_armEndFinset ω n x = bk2_armEndFinset ω n y := by
-- proof
  apply StatMech.Percolation.daec_armEnds_eq_of_connected ω n hxy

/--
[daec_not_disjoint_of_connected_trif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsClose.lean)
-/
@[path]
private lemma daec_not_disjoint_of_connected_trif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x y : Site d}
-- given
  (hn : 1 ≤ n)
  (hxbox : x ∈ box d n)
  (htri : IsTrifurcation d ω x)
  (_hybox : y ∈ box d n)
  (_htriy : IsTrifurcation d ω y)
  (hconn : Connected d ω x y) :
-- imply
  ¬ Disjoint (bk2_armEndFinset ω n x) (bk2_armEndFinset ω n y) := by
-- proof
  apply StatMech.Percolation.daec_not_disjoint_of_connected_trif ω n hn hxbox htri _hybox _htriy hconn

/--
[daec_disjointArmEnds_false_of_connected_trif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsClose.lean)
-/
@[path]
private lemma daec_disjointArmEnds_false_of_connected_trif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x y : Site d}
-- given
  (hn : 1 ≤ n)
  (hxbox : x ∈ box d n)
  (htri : IsTrifurcation d ω x)
  (hybox : y ∈ box d n)
  (htriy : IsTrifurcation d ω y)
  (hxy : x ≠ y)
  (hconn : Connected d ω x y) :
-- imply
  ¬ bk2_DisjointArmEnds ω n := by
-- proof
  apply StatMech.Percolation.daec_disjointArmEnds_false_of_connected_trif ω n hn hxbox htri hybox htriy hxy hconn

/--
[daec_disjointArmEnds_forces_separation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsClose.lean)
-/
@[path]
private lemma daec_disjointArmEnds_forces_separation_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (hdisj : bk2_DisjointArmEnds ω n) :
-- imply
  ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y → x ≠ y → ¬ Connected d ω x y := by
-- proof
  apply StatMech.Percolation.daec_disjointArmEnds_forces_separation ω n hn hdisj

/--
[daec_disjointArmEnds_refutable_on_spanned](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsClose.lean)
-/
@[path]
private lemma daec_disjointArmEnds_refutable_on_spanned_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x y : Site d}
-- given
  (hn : 1 ≤ n)
  (hxbox : x ∈ box d n)
  (htri : IsTrifurcation d ω x)
  (hybox : y ∈ box d n)
  (htriy : IsTrifurcation d ω y)
  (hxy : x ≠ y)
  (hspan : ∀ u v, u ∈ box d n → IsTrifurcation d ω u → v ∈ box d n → IsTrifurcation d ω v → Connected d ω u v) :
-- imply
  ¬ bk2_DisjointArmEnds ω n := by
-- proof
  apply StatMech.Percolation.daec_disjointArmEnds_refutable_on_spanned ω n hn hxbox htri hybox htriy hxy hspan

/--
[daec_trif_removeSite_three_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsClose.lean)
-/
@[path]
private lemma daec_trif_removeSite_three_distinct_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x a₁ a₂ a₃ : Site d}
-- given
  (hn : 1 ≤ n)
  (hx : Connected d ω x a₁)
  (hx2 : Connected d ω x a₂)
  (hx3 : Connected d ω x a₃)
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
  ∃ z₁ z₂ z₃ : Site d, (z₁ ∈ vertexBoundary d n ∧ z₂ ∈ vertexBoundary d n ∧ z₃ ∈ vertexBoundary d n) ∧ (Connected d ω x z₁ ∧ Connected d ω x z₂ ∧ Connected d ω x z₃) ∧ (¬ Connected d (removeSite x ω) z₁ z₂ ∧ ¬ Connected d (removeSite x ω) z₁ z₃ ∧ ¬ Connected d (removeSite x ω) z₂ z₃) ∧ (z₁ ≠ z₂ ∧ z₁ ≠ z₃ ∧ z₂ ≠ z₃) := by
-- proof
  apply StatMech.Percolation.daec_trif_removeSite_three_distinct ω n hn hx hx2 hx3 ha1box ha2box ha3box hi1 hi2 hi3 hd12 hd13 hd23

/--
[daec_forestLeafInjection_iff_distinctArmEnds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsClose.lean)
-/
@[path]
private lemma daec_forestLeafInjection_iff_distinctArmEnds_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ} :
-- imply
  daec_ForestLeafInjection ω n ↔ tfc_DistinctArmEnds ω n := by
-- proof
  apply StatMech.Percolation.daec_forestLeafInjection_iff_distinctArmEnds ω n

/--
[daec_distinctArmEnds_of_forestLeafInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsClose.lean)
-/
@[path]
private lemma daec_distinctArmEnds_of_forestLeafInjection_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : daec_ForestLeafInjection ω n) :
-- imply
  tfc_DistinctArmEnds ω n := by
-- proof
  apply StatMech.Percolation.daec_distinctArmEnds_of_forestLeafInjection ω n h

/--
[daec_forestLeafInjection_of_subsingleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsClose.lean)
-/
@[path]
private lemma daec_forestLeafInjection_of_subsingleton_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (hsub : ∀ x y, x ∈ box d n → IsTrifurcation d ω x → y ∈ box d n → IsTrifurcation d ω y → x = y) :
-- imply
  daec_ForestLeafInjection ω n := by
-- proof
  apply StatMech.Percolation.daec_forestLeafInjection_of_subsingleton ω n hn hsub

/--
[daec_Tcount_le_boundary_of_forestLeafInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsClose.lean)
-/
@[path]
private lemma daec_Tcount_le_boundary_of_forestLeafInjection_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : daec_ForestLeafInjection ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.daec_Tcount_le_boundary_of_forestLeafInjection ω n h

/--
[daec_forestLeafInjection_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsClose.lean)
-/
@[path]
private lemma daec_forestLeafInjection_of_disjoint_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (hdisj : bk2_DisjointArmEnds ω n) :
-- imply
  daec_ForestLeafInjection ω n := by
-- proof
  apply StatMech.Percolation.daec_forestLeafInjection_of_disjoint ω n hn hdisj

/--
[daec_burton_keane_bernoulli](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsClose.lean)
-/
@[path]
private lemma daec_burton_keane_bernoulli_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : NNReal)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → daec_ForestLeafInjection ω n)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Percolation.daec_burton_keane_bernoulli hd p hp1 hp0 hres htrif


-- created on 2026-10-23
