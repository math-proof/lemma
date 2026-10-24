import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bc54coarse
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc54_globalArmForest_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc54coarse.lean)
-/
@[path]
private lemma bc54_globalArmForest_succ_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (hcanon : ∀ x, x ∈ box d n → IsTrifurcation d ω x → IsCanonicalTrifurcation d ω x)
  (hexists : ∃ x, x ∈ box d n ∧ IsTrifurcation d ω x) :
-- imply
  dfc_ArmForestReachingSucc ω n := by
-- proof
  apply StatMech.Walls.bc54_globalArmForest_succ ω n hn hcanon hexists

/--
[bc54_canonGlobalArmForest_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc54coarse.lean)
-/
@[path]
private lemma bc54_canonGlobalArmForest_succ_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (hexists : ∃ x, x ∈ box d n ∧ IsCanonicalTrifurcation d ω x) :
-- imply
  dfc_CanonArmForestReachingSucc ω n := by
-- proof
  apply StatMech.Walls.bc54_canonGlobalArmForest_succ ω n hn hexists

/--
[bc54_Tcount_le_boundary_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc54coarse.lean)
-/
@[path]
private lemma bc54_Tcount_le_boundary_succ_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (hcanon : ∀ x, x ∈ box d n → IsTrifurcation d ω x → IsCanonicalTrifurcation d ω x) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d (n + 1) := by
-- proof
  apply StatMech.Walls.bc54_Tcount_le_boundary_succ ω n hn hcanon

/--
[bc54_canonTcount_le_boundary_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc54coarse.lean)
-/
@[path]
private lemma bc54_canonTcount_le_boundary_succ_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  ctc2_canonTcount d ω n ≤ boxSV_boundaryCard d (n + 1) := by
-- proof
  apply StatMech.Walls.bc54_canonTcount_le_boundary_succ ω n hn

/--
[bc54_classicalTcount_le_boundary_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc54coarse.lean)
-/
@[path]
private lemma bc54_classicalTcount_le_boundary_succ_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  bc48_Tcount_classical d ω n ≤ boxSV_boundaryCard d (n + 1) := by
-- proof
  apply StatMech.Walls.bc54_classicalTcount_le_boundary_succ ω n hn

/--
[bc54_classicalTcount_le_boundary_succ_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc54coarse.lean)
-/
@[path]
private lemma bc54_classicalTcount_le_boundary_succ_all_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  bc48_Tcount_classical d ω n ≤ boxSV_boundaryCard d (n + 1) := by
-- proof
  apply StatMech.Walls.bc54_classicalTcount_le_boundary_succ_all ω hd n

/--
[bc54_boundary_succ_vol_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc54coarse.lean)
-/
@[path]
private lemma bc54_boundary_succ_vol_tendsto_eq
  {d : ℕ}
  {d : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  Tendsto (fun n => (boxSV_boundaryCard d (n + 1) : ℝ) / ((boxFinsetBK d n).card : ℝ)) atTop (𝓝 0) := by
-- proof
  apply StatMech.Walls.bc54_boundary_succ_vol_tendsto d hd

/--
[bc54_classicalTrif_prob_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc54coarse.lean)
-/
@[path]
private lemma bc54_classicalTrif_prob_eq_zero_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (hd : 1 ≤ d)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) :
-- imply
  μ {ω | bc47_IsClassicalTrifurcation ω 0} = 0 := by
-- proof
  apply StatMech.Walls.bc54_classicalTrif_prob_eq_zero μ hd hinv

/--
[bc54_burton_keane_bernoulli](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc54coarse.lean)
-/
@[path]
private lemma bc54_burton_keane_bernoulli_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hroute : ∀ n : ℕ, 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (threeMeetBox d n) → ∃ a₁ a₂ a₃ : Site d, 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (NeighborTrifPrecursor d a₁ a₂ a₃)) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc54_burton_keane_bernoulli hd p hp1 hp0 hroute

/--
[bc54_witness_boundary_trif_arm_inbox_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc54coarse.lean)
-/
@[path]
private lemma bc54_witness_boundary_trif_arm_inbox_succ_eq
  {d : ℕ} :
-- imply
  (![(2 : ℤ), 0] : Site 2) ∈ box 2 (1 + 1) := by
-- proof
  apply StatMech.Walls.bc54_witness_boundary_trif_arm_inbox_succ

/--
[bc54_witness_arm_outside_box_n](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc54coarse.lean)
-/
@[path]
private lemma bc54_witness_arm_outside_box_n_eq
  {d : ℕ} :
-- imply
  (![(2 : ℤ), 0] : Site 2) ∉ box 2 1 := by
-- proof
  apply StatMech.Walls.bc54_witness_arm_outside_box_n

/--
[bc54_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc54coarse.lean)
-/
@[path]
private lemma bc54_status_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), bc48_Tcount_classical d ω n ≤ boxSV_boundaryCard d (n + 1)) ∧ (Tendsto (fun n => (boxSV_boundaryCard d (n + 1) : ℝ) / ((boxFinsetBK d n).card : ℝ)) atTop (𝓝 0)) ∧ (∀ (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ], IsTranslationInvariant (G := Multiplicative (Site d)) μ → μ {ω | bc47_IsClassicalTrifurcation ω 0} = 0) := by
-- proof
  apply StatMech.Walls.bc54_status hd


-- created on 2026-10-23
