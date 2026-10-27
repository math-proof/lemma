import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Percolation.LeafHallClose.Part2
open Set SimpleGraph Finset MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[lhc_mem_trace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LeafHallClose.lean)
-/
@[path]
private lemma lhc_mem_trace_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ z : Site d} :
-- imply
  z ∈ lhc_trace ω n x₀ ↔ z ∈ vertexBoundary d n ∧ Connected d ω x₀ z := by
-- proof
  apply StatMech.Percolation.lhc_mem_trace

/--
[lhc_trace_card_le_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LeafHallClose.lean)
-/
@[path]
private lemma lhc_trace_card_le_boundary_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ : Site d} :
-- imply
  (lhc_trace ω n x₀).card ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.lhc_trace_card_le_boundary ω n x₀

/--
[lhc_two_le_trace_of_forestLeafSelection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LeafHallClose.lean)
-/
@[path]
private lemma lhc_two_le_trace_of_forestLeafSelection_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ : Site d}
-- given
  (hconn : ∀ x, x ∈ box d n → IsTrifurcation d ω x → Connected d ω x₀ x)
  (h : str_ForestLeafSelection ω n) :
-- imply
  2 * Tcount d ω n ≤ (lhc_trace ω n x₀).card := by
-- proof
  apply StatMech.Percolation.lhc_two_le_trace_of_forestLeafSelection ω n x₀ hconn h

/--
[lhc_twice_Tcount_succ_le_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LeafHallClose.lean)
-/
@[path]
private lemma lhc_twice_Tcount_succ_le_boundary_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : str_ForestLeafSelection ω n) :
-- imply
  2 * Tcount d ω n + 1 ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.lhc_twice_Tcount_succ_le_boundary ω n h

/--
[lhc_not_forestLeafSelection_of_clawTrace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LeafHallClose.lean)
-/
@[path]
private lemma lhc_not_forestLeafSelection_of_clawTrace_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hclaw : lhc_ConnectedClawTrace ω n) :
-- imply
  ¬ str_ForestLeafSelection ω n := by
-- proof
  apply StatMech.Percolation.lhc_not_forestLeafSelection_of_clawTrace ω n hclaw

/--
[lhc_clawTrace_excludes_forestLeafSelection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LeafHallClose.lean)
-/
@[path]
private lemma lhc_clawTrace_excludes_forestLeafSelection_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hclaw : lhc_ConnectedClawTrace ω n)
  (h : str_ForestLeafSelection ω n) :
-- imply
  False := by
-- proof
  apply StatMech.Percolation.lhc_clawTrace_excludes_forestLeafSelection ω n hclaw h

/--
[lhc_clawTrace_card_consistent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LeafHallClose.lean)
-/
@[path]
private lemma lhc_clawTrace_card_consistent_eq
  {d : ℕ}
  {T : ℕ}
-- given
  (hT : 3 ≤ T) :
-- imply
  T + 2 ≤ T + 2 ∧ T + 2 < 2 * T := by
-- proof
  apply StatMech.Percolation.lhc_clawTrace_card_consistent hT

/--
[lhc_clawTrace_of_smallTrace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LeafHallClose.lean)
-/
@[path]
private lemma lhc_clawTrace_of_smallTrace_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ : Site d}
-- given
  (hconn : ∀ x, x ∈ box d n → IsTrifurcation d ω x → Connected d ω x₀ x)
  (hsmall : (lhc_trace ω n x₀).card < 2 * Tcount d ω n) :
-- imply
  lhc_ConnectedClawTrace ω n := by
-- proof
  apply StatMech.Percolation.lhc_clawTrace_of_smallTrace ω n x₀ hconn hsmall

/--
[lhc_boundaryArmInjection_of_forestLeafSelection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LeafHallClose.lean)
-/
@[path]
private lemma lhc_boundaryArmInjection_of_forestLeafSelection_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : str_ForestLeafSelection ω n) :
-- imply
  tfc_BoundaryArmInjection ω n := by
-- proof
  apply StatMech.Percolation.lhc_boundaryArmInjection_of_forestLeafSelection ω n h

/--
[lhc_Tcount_le_boundary_of_boundaryArmInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LeafHallClose.lean)
-/
@[path]
private lemma lhc_Tcount_le_boundary_of_boundaryArmInjection_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : tfc_BoundaryArmInjection ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.lhc_Tcount_le_boundary_of_boundaryArmInjection ω n h

/--
[lhc_Tcount_le_boundary_of_forestLeafSelection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LeafHallClose.lean)
-/
@[path]
private lemma lhc_Tcount_le_boundary_of_forestLeafSelection_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : str_ForestLeafSelection ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.lhc_Tcount_le_boundary_of_forestLeafSelection ω n h

/--
[lhc_boundaryArmInjection_of_uniqueTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LeafHallClose.lean)
-/
@[path]
private lemma lhc_boundaryArmInjection_of_uniqueTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {r a : Site d}
-- given
  (ha : a ∈ vertexBoundary d n)
  (hsingle : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = r) :
-- imply
  tfc_BoundaryArmInjection ω n := by
-- proof
  apply StatMech.Percolation.lhc_boundaryArmInjection_of_uniqueTrif ω n ha hsingle

/--
[lhc_burton_keane_bernoulli_of_boundaryArmInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LeafHallClose.lean)
-/
@[path]
private lemma lhc_burton_keane_bernoulli_of_boundaryArmInjection_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → tfc_BoundaryArmInjection ω n)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Percolation.lhc_burton_keane_bernoulli_of_boundaryArmInjection hd p hp1 hp0 hres htrif


-- created on 2026-10-23
