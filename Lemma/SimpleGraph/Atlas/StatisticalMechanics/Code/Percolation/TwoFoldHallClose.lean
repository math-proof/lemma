import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Percolation.TwoFoldHallClose.Part2
open Set SimpleGraph Finset MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[tfh_twoFold_hall_root](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TwoFoldHallClose.lean)
-/
@[path]
private lemma tfh_twoFold_hall_root_eq
  {d : ℕ}
  [DecidableEq V]
  {T : Finset V}
  {rootEnds : Finset V}
  {armEnds : V → Fin 2 → Finset V}
-- given
  (hrne : rootEnds.Nonempty)
  (hne : ∀ x ∈ T, ∀ i, (armEnds x i).Nonempty)
  (hrdisj : ∀ x ∈ T, ∀ i, Disjoint rootEnds (armEnds x i))
  (hdisj : ∀ x ∈ T, ∀ i, ∀ y ∈ T, ∀ j, (x, i) ≠ (y, j) → Disjoint (armEnds x i) (armEnds y j)) :
-- imply
  ∃ (r₀ : V) (ℓ : V → Fin 2 → V), r₀ ∈ rootEnds ∧ (∀ x ∈ T, ∀ i, ℓ x i ∈ armEnds x i) ∧ (∀ x ∈ T, ∀ i, ℓ x i ≠ r₀) ∧ (∀ x ∈ T, ∀ i, ∀ y ∈ T, ∀ j, ℓ x i = ℓ y j → x = y ∧ i = j) := by
-- proof
  apply StatMech.Percolation.tfh_twoFold_hall_root T rootEnds armEnds hrne hne hrdisj hdisj

/--
[tfh_forestLeafSelection_of_twoFoldForestArms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TwoFoldHallClose.lean)
-/
@[path]
private lemma tfh_forestLeafSelection_of_twoFoldForestArms_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (h : tfh_TwoFoldForestArms ω n) :
-- imply
  str_ForestLeafSelection ω n := by
-- proof
  apply StatMech.Percolation.tfh_forestLeafSelection_of_twoFoldForestArms ω n hn h

/--
[tfh_twoFoldForestArms_of_uniqueTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TwoFoldHallClose.lean)
-/
@[path]
private lemma tfh_twoFoldForestArms_of_uniqueTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ a₀ a₁ a₂ : Site d}
-- given
  (hx0box : x₀ ∈ box d n)
  (htri0 : IsTrifurcation d ω x₀)
  (ha0box : a₀ ∈ box d n)
  (ha1box : a₁ ∈ box d n)
  (ha2box : a₂ ∈ box d n)
  (hc0 : Connected d ω x₀ a₀)
  (hc1 : Connected d ω x₀ a₁)
  (hinf0 : (cluster d (removeSite x₀ ω) a₀).Infinite)
  (hinf1 : (cluster d (removeSite x₀ ω) a₁).Infinite)
  (hinf2 : (cluster d (removeSite x₀ ω) a₂).Infinite)
  (hsep01 : ¬ Connected d (removeSite x₀ ω) a₀ a₁)
  (hsep0r : ¬ Connected d (removeSite x₀ ω) a₂ a₀)
  (hsep1r : ¬ Connected d (removeSite x₀ ω) a₂ a₁)
  (huniq : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀) :
-- imply
  tfh_TwoFoldForestArms ω n := by
-- proof
  apply StatMech.Percolation.tfh_twoFoldForestArms_of_uniqueTrif ω n hx0box htri0 ha0box ha1box ha2box hc0 hc1 hinf0 hinf1 hinf2 hsep01 hsep0r hsep1r huniq

/--
[tfh_spanningTreeLeafCount_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TwoFoldHallClose.lean)
-/
@[path]
private lemma tfh_spanningTreeLeafCount_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {z₀ z₁ : Site d}
-- given
  (hz₀ : z₀ ∈ vertexBoundary d n)
  (hz₁ : z₁ ∈ vertexBoundary d n)
  (hzne : z₀ ≠ z₁)
  (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  flc2_SpanningTreeLeafCount ω n := by
-- proof
  apply StatMech.Percolation.tfh_spanningTreeLeafCount_of_noTrif ω n hz₀ hz₁ hzne hno

/--
[tfh_spanningTreeLeafCount_of_twoFoldForestArms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TwoFoldHallClose.lean)
-/
@[path]
private lemma tfh_spanningTreeLeafCount_of_twoFoldForestArms_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (h : tfh_TwoFoldForestArms ω n)
  (hbase : (∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) → flc2_SpanningTreeLeafCount ω n) :
-- imply
  flc2_SpanningTreeLeafCount ω n := by
-- proof
  apply StatMech.Percolation.tfh_spanningTreeLeafCount_of_twoFoldForestArms ω n hn h hbase

/--
[tfh_Tcount_le_boundary_of_twoFoldForestArms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TwoFoldHallClose.lean)
-/
@[path]
private lemma tfh_Tcount_le_boundary_of_twoFoldForestArms_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (h : tfh_TwoFoldForestArms ω n)
  (hbase : (∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) → flc2_SpanningTreeLeafCount ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.tfh_Tcount_le_boundary_of_twoFoldForestArms ω n hn h hbase

/--
[tfh_spanningTree_of_twoFoldForestArms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TwoFoldHallClose.lean)
-/
@[path]
private lemma tfh_spanningTree_of_twoFoldForestArms_eq
  {d : ℕ}
-- given
  (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → tfh_TwoFoldForestArms ω n)
  (hbase : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → (∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) → flc2_SpanningTreeLeafCount ω n) :
-- imply
  ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → flc2_SpanningTreeLeafCount ω n := by
-- proof
  apply StatMech.Percolation.tfh_spanningTree_of_twoFoldForestArms hres hbase

/--
[tfh_burton_keane_bernoulli_of_twoFoldForestArms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TwoFoldHallClose.lean)
-/
@[path]
private lemma tfh_burton_keane_bernoulli_of_twoFoldForestArms_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → tfh_TwoFoldForestArms ω n)
  (hbase : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → (∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) → flc2_SpanningTreeLeafCount ω n)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Percolation.tfh_burton_keane_bernoulli_of_twoFoldForestArms hd p hp1 hp0 hres hbase htrif


-- created on 2026-10-23
