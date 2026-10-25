import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc9distinctcutclusters
open Set SimpleGraph StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech StatMech.Walls


/--
[bc9_distinctCutClusters](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc9distinctcutclusters.lean)
-/
@[path]
private lemma bc9_distinctCutClusters_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  bc9_DistinctCutClusters d n := by
-- proof
  apply StatMech.Walls.bc9_distinctCutClusters n

/--
[bc9_threeArms_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc9distinctcutclusters.lean)
-/
@[path]
private lemma bc9_threeArms_distinct_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hω : ω ∈ threeMeetBox d n) :
-- imply
  ∃ x₁ x₂ x₃ : Site d, (cluster d (removeSite 0 ω) x₁).Infinite ∧ (cluster d (removeSite 0 ω) x₂).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite ∧ cluster d (removeSite 0 ω) x₁ ≠ cluster d (removeSite 0 ω) x₂ ∧ cluster d (removeSite 0 ω) x₁ ≠ cluster d (removeSite 0 ω) x₃ ∧ cluster d (removeSite 0 ω) x₂ ≠ cluster d (removeSite 0 ω) x₃ := by
-- proof
  apply StatMech.Walls.bc9_threeArms_distinct n ω hω

/--
[bc9_cut_no_crossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc9distinctcutclusters.lean)
-/
@[path]
private lemma bc9_cut_no_crossing_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : Site d}
-- given
  (hne : cluster d (removeSite 0 ω) x ≠ cluster d (removeSite 0 ω) y) :
-- imply
  ∀ ⦃u : Site d⦄, u ∈ cluster d (removeSite 0 ω) x → ∀ ⦃v : Site d⦄, v ∈ cluster d (removeSite 0 ω) y → ¬ IsOpenEdge d (removeSite 0 ω) u v := by
-- proof
  apply StatMech.Walls.bc9_cut_no_crossing ω hne

/--
[bc9_threeArms_pairwiseNoMerge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc9distinctcutclusters.lean)
-/
@[path]
private lemma bc9_threeArms_pairwiseNoMerge_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hω : ω ∈ threeMeetBox d n) :
-- imply
  ∃ x₁ x₂ x₃ : Site d, (cluster d (removeSite 0 ω) x₁).Infinite ∧ (cluster d (removeSite 0 ω) x₂).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite ∧ cluster d (removeSite 0 ω) x₁ ≠ cluster d (removeSite 0 ω) x₂ ∧ cluster d (removeSite 0 ω) x₁ ≠ cluster d (removeSite 0 ω) x₃ ∧ cluster d (removeSite 0 ω) x₂ ≠ cluster d (removeSite 0 ω) x₃ ∧ Disjoint (cluster d (removeSite 0 ω) x₁) (cluster d (removeSite 0 ω) x₂) ∧ Disjoint (cluster d (removeSite 0 ω) x₁) (cluster d (removeSite 0 ω) x₃) ∧ Disjoint (cluster d (removeSite 0 ω) x₂) (cluster d (removeSite 0 ω) x₃) ∧ (∀ ⦃u : Site d⦄, u ∈ cluster d (removeSite 0 ω) x₁ → ∀ ⦃v : Site d⦄, v ∈ cluster d (removeSite 0 ω) x₂ → ¬ IsOpenEdge d (removeSite 0 ω) u v) ∧ (∀ ⦃u : Site d⦄, u ∈ cluster d (removeSite 0 ω) x₁ → ∀ ⦃v : Site d⦄, v ∈ cluster d (removeSite 0 ω) x₃ → ¬ IsOpenEdge d (removeSite 0 ω) u v) ∧ (∀ ⦃u : Site d⦄, u ∈ cluster d (removeSite 0 ω) x₂ → ∀ ⦃v : Site d⦄, v ∈ cluster d (removeSite 0 ω) x₃ → ¬ IsOpenEdge d (removeSite 0 ω) u v) := by
-- proof
  apply StatMech.Walls.bc9_threeArms_pairwiseNoMerge n ω hω

/--
[bc9_noCrossing_of_node](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc9distinctcutclusters.lean)
-/
@[path]
private lemma bc9_noCrossing_of_node_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : Site d} :
-- imply
  bc8_NoCrossing ω x y := by
-- proof
  apply StatMech.Walls.bc9_noCrossing_of_node ω x y

/--
[bc9_distinctCutClusters_originRewiring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc9distinctcutclusters.lean)
-/
@[path]
private lemma bc9_distinctCutClusters_originRewiring_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hrw : bc8_OriginRewiring d n)
  (hω : ω ∈ threeMeetBox d n) :
-- imply
  ∃ W : Finset (Sym2 (Site d)), (∀ e ∈ W, (0 : Site d) ∉ e) ∧ IsCanonicalTrifurcation d (forceOpenFinset W ω) 0 := by
-- proof
  apply StatMech.Walls.bc9_distinctCutClusters_originRewiring n hrw ω hω


-- created on 2026-10-23
