import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Percolation.BKHallSDRClose.Part2
open Set SimpleGraph Finset MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[bhs_exists_injOn_of_hall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKHallSDRClose.lean)
-/
@[path]
private lemma bhs_exists_injOn_of_hall_eq
  {d : ℕ}
  [DecidableEq V]
  {T : Finset V}
  {armEnds : V → Finset V}
-- given
  (hHall : ∀ S : Finset V, S ⊆ T → S.card ≤ (S.biUnion armEnds).card) :
-- imply
  ∃ φ : V → V, (∀ x ∈ T, φ x ∈ armEnds x) ∧ Set.InjOn φ T := by
-- proof
  apply StatMech.Percolation.bhs_exists_injOn_of_hall T armEnds hHall

/--
[bhs_hall_of_pairwiseDisjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKHallSDRClose.lean)
-/
@[path]
private lemma bhs_hall_of_pairwiseDisjoint_eq
  {d : ℕ}
  [DecidableEq V]
  {T : Finset V}
  {armEnds : V → Finset V}
-- given
  (hne : ∀ x ∈ T, (armEnds x).Nonempty)
  (hdisj : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → Disjoint (armEnds x) (armEnds y)) :
-- imply
  ∀ S : Finset V, S ⊆ T → S.card ≤ (S.biUnion armEnds).card := by
-- proof
  apply StatMech.Percolation.bhs_hall_of_pairwiseDisjoint T armEnds hne hdisj

/--
[bhs_distinctArmEnds_of_hall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKHallSDRClose.lean)
-/
@[path]
private lemma bhs_distinctArmEnds_of_hall_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : bhs_HallArmEnds ω n) :
-- imply
  tfc_DistinctArmEnds ω n := by
-- proof
  apply StatMech.Percolation.bhs_distinctArmEnds_of_hall ω n h

/--
[bhs_Tcount_le_boundary_of_hall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKHallSDRClose.lean)
-/
@[path]
private lemma bhs_Tcount_le_boundary_of_hall_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : bhs_HallArmEnds ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.bhs_Tcount_le_boundary_of_hall ω n h

/--
[bhs_hallArmEnds_of_globalCutSeparation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKHallSDRClose.lean)
-/
@[path]
private lemma bhs_hallArmEnds_of_globalCutSeparation_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (h : daep_GlobalCutSeparation ω n) :
-- imply
  bhs_HallArmEnds ω n := by
-- proof
  apply StatMech.Percolation.bhs_hallArmEnds_of_globalCutSeparation ω n hn h

/--
[bhs_hallArmEnds_of_singleCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKHallSDRClose.lean)
-/
@[path]
private lemma bhs_hallArmEnds_of_singleCut_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (h : daep2_SingleCutBranchSeparation ω n) :
-- imply
  bhs_HallArmEnds ω n := by
-- proof
  apply StatMech.Percolation.bhs_hallArmEnds_of_singleCut ω n hn h

/--
[bhs_hallArmEnds_of_disjointSep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKHallSDRClose.lean)
-/
@[path]
private lemma bhs_hallArmEnds_of_disjointSep_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {b : Site d → Site d}
-- given
  (hn : 1 ≤ n)
  (hexist : ∀ x, x ∈ box d n → IsTrifurcation d ω x → b x ∈ box d n ∧ Connected d ω x (b x) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite)
  (hsep : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y → x ≠ y → ¬ Connected d (removeSites (tfc_trifFinset ω n) ω) (b x) (b y)) :
-- imply
  bhs_HallArmEnds ω n := by
-- proof
  apply StatMech.Percolation.bhs_hallArmEnds_of_disjointSep ω n hn b hexist hsep

/--
[bhs_hallArmEnds_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKHallSDRClose.lean)
-/
@[path]
private lemma bhs_hallArmEnds_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  bhs_HallArmEnds ω n := by
-- proof
  apply StatMech.Percolation.bhs_hallArmEnds_of_noTrif ω n hno

/--
[bhs_burton_keane_bernoulli_of_hall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKHallSDRClose.lean)
-/
@[path]
private lemma bhs_burton_keane_bernoulli_of_hall_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bhs_HallArmEnds ω n)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Percolation.bhs_burton_keane_bernoulli_of_hall hd p hp1 hp0 hres htrif


-- created on 2026-10-23
