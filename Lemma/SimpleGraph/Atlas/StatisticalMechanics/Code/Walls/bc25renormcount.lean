import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc25renormcount
open Set SimpleGraph MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Walls


/--
[bc25_isTrifurcation_of_coarseTrif_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc25renormcount.lean)
-/
@[path]
private lemma bc25_isTrifurcation_of_coarseTrif_zero_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : IsCoarseTrifurcation d 0 ω) :
-- imply
  IsTrifurcation d ω (0 : Site d) := by
-- proof
  apply StatMech.Walls.bc25_isTrifurcation_of_coarseTrif_zero h

/--
[bc25_coarseTrif_zero_chain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc25renormcount.lean)
-/
@[path]
private lemma bc25_coarseTrif_zero_chain_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  (IsCanonicalTrifurcation d ω (0 : Site d) → IsCoarseTrifurcation d 0 ω) ∧ (IsCoarseTrifurcation d 0 ω → IsTrifurcation d ω (0 : Site d)) := by
-- proof
  apply StatMech.Walls.bc25_coarseTrif_zero_chain

/--
[bc25_bridge_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc25renormcount.lean)
-/
@[path]
private lemma bc25_bridge_nonvacuous_eq
  {d : ℕ} :
-- imply
  ∃ ω : ConfigSpace (Sym2 (Site 2)), IsCoarseTrifurcation 2 0 ω ∧ IsTrifurcation 2 ω (0 : Site 2) := by
-- proof
  apply StatMech.Walls.bc25_bridge_nonvacuous

/--
[bc25_Tcount_le_boundary_of_globalForestArms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc25renormcount.lean)
-/
@[path]
private lemma bc25_Tcount_le_boundary_of_globalForestArms_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (h : aed_GlobalForestArms ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Walls.bc25_Tcount_le_boundary_of_globalForestArms ω n hn h

/--
[bc25_Tcount_le_boundary_of_forestPeel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc25renormcount.lean)
-/
@[path]
private lemma bc25_Tcount_le_boundary_of_forestPeel_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (h : bkfl_ForestPeel ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Walls.bc25_Tcount_le_boundary_of_forestPeel ω n hn h

/--
[bc25_Tcount_zero_le_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc25renormcount.lean)
-/
@[path]
private lemma bc25_Tcount_zero_le_box_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  Tcount d ω 0 ≤ (boxFinsetBK d 0).card := by
-- proof
  apply StatMech.Walls.bc25_Tcount_zero_le_box ω

/--
[bc25_burton_keane_uniqueness_of_forest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc25renormcount.lean)
-/
@[path]
private lemma bc25_burton_keane_uniqueness_of_forest_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (herg : IsErgodic (G := Multiplicative (Site d)) μ)
  (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → aed_GlobalForestArms ω n)
  (hdens : Filter.Tendsto (fun n => (boxSV_boundaryCard d n : ℝ) / ((boxFinsetBK d n).card : ℝ)) Filter.atTop (nhds 0))
  (htrif : 0 < μ {ω | numInfiniteClusters d ω = ⊤} → 0 < μ {ω | IsTrifurcation d ω 0})
  (hmerge : μ (atLeastTwoInfinite d) = 0) :
-- imply
  ∃ k : ℕ∞, k ≤ 1 ∧ μ {ω | numInfiniteClusters d ω = k} = 1 ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc25_burton_keane_uniqueness_of_forest μ herg hres hdens htrif hmerge

/--
[bc25_burton_keane_bernoulli_of_forest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc25renormcount.lean)
-/
@[path]
private lemma bc25_burton_keane_bernoulli_of_forest_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → aed_GlobalForestArms ω n)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc25_burton_keane_bernoulli_of_forest hd p hp1 hp0 hres htrif


-- created on 2026-10-23
