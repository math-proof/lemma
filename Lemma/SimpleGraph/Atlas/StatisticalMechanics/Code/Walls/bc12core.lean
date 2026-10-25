import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc12core.Part2
open Set SimpleGraph StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation MeasureTheory StatMech StatMech.Walls


/--
[bc12_cluster_ne_of_not_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc12core.lean)
-/
@[path]
private lemma bc12_cluster_ne_of_not_connected_eq
  {d : ℕ}
  {σ : ConfigSpace (Sym2 (Site d))}
  {a b : Site d}
-- given
  (h : ¬ Connected d σ a b) :
-- imply
  cluster d σ a ≠ cluster d σ b := by
-- proof
  apply StatMech.Walls.bc12_cluster_ne_of_not_connected h

/--
[bc12_openAdj_forceOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc12core.lean)
-/
@[path]
private lemma bc12_openAdj_forceOpen_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {W : Finset (Sym2 (Site d))}
  {a b : Site d}
-- given
  (h : (openSubgraph d ω).Adj a b) :
-- imply
  (openSubgraph d (forceOpenFinset W ω)).Adj a b := by
-- proof
  apply StatMech.Walls.bc12_openAdj_forceOpen W h

/--
[bc12_canonicalTrif_discharges_boxReach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc12core.lean)
-/
@[path]
private lemma bc12_canonicalTrif_discharges_boxReach_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (htri : IsCanonicalTrifurcation d ω 0) :
-- imply
  ∃ W : Finset (Sym2 (Site d)), (∀ e ∈ W, (0 : Site d) ∉ e) ∧ ∃ y₁ y₂ y₃ : Site d, y₁ ≠ 0 ∧ y₂ ≠ 0 ∧ y₃ ≠ 0 ∧ Connected d (forceOpenFinset W ω) 0 y₁ ∧ Connected d (forceOpenFinset W ω) 0 y₂ ∧ Connected d (forceOpenFinset W ω) 0 y₃ ∧ (cluster d (removeSite 0 (forceOpenFinset W ω)) y₁).Infinite ∧ (cluster d (removeSite 0 (forceOpenFinset W ω)) y₂).Infinite ∧ (cluster d (removeSite 0 (forceOpenFinset W ω)) y₃).Infinite ∧ cluster d (removeSite 0 (forceOpenFinset W ω)) y₁ ≠ cluster d (removeSite 0 (forceOpenFinset W ω)) y₂ ∧ cluster d (removeSite 0 (forceOpenFinset W ω)) y₁ ≠ cluster d (removeSite 0 (forceOpenFinset W ω)) y₃ ∧ cluster d (removeSite 0 (forceOpenFinset W ω)) y₂ ≠ cluster d (removeSite 0 (forceOpenFinset W ω)) y₃ := by
-- proof
  apply StatMech.Walls.bc12_canonicalTrif_discharges_boxReach ω htri

/--
[bc12_boxOriginReach_of_trifurcation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc12core.lean)
-/
@[path]
private lemma bc12_boxOriginReach_of_trifurcation_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : bc12_BoxOriginTrifurcation d n) :
-- imply
  bc9_BoxOriginReach d n := by
-- proof
  apply StatMech.Walls.bc12_boxOriginReach_of_trifurcation n h

/--
[bc12_originRewiring_of_trifurcation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc12core.lean)
-/
@[path]
private lemma bc12_originRewiring_of_trifurcation_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : bc12_BoxOriginTrifurcation d n) :
-- imply
  bc8_OriginRewiring d n := by
-- proof
  apply StatMech.Walls.bc12_originRewiring_of_trifurcation n h

/--
[bc12_canonicalTrif_of_trifurcation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc12core.lean)
-/
@[path]
private lemma bc12_canonicalTrif_of_trifurcation_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : bc12_BoxOriginTrifurcation d n)
  (hω : ω ∈ threeMeetBox d n) :
-- imply
  ∃ W : Finset (Sym2 (Site d)), (∀ e ∈ W, (0 : Site d) ∉ e) ∧ IsCanonicalTrifurcation d (forceOpenFinset W ω) 0 := by
-- proof
  apply StatMech.Walls.bc12_canonicalTrif_of_trifurcation n h ω hω

/--
[bc12_burtonKeane_uniqueness_of_trifurcation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc12core.lean)
-/
@[path]
private lemma bc12_burtonKeane_uniqueness_of_trifurcation_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {bdry : ℕ → ℕ}
-- given
  (herg : IsErgodic (G := Multiplicative (Site d)) μ)
  (hfe : HasFiniteEnergyMerge μ)
  (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
  (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
  (hdens : Filter.Tendsto (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ)) Filter.atTop (nhds 0))
  (hr : ∀ n : ℕ, bc12_BoxOriginTrifurcation d n) :
-- imply
  (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1) ∧ μ (atLeastTwoInfinite d) = 0 ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc12_burtonKeane_uniqueness_of_trifurcation μ herg hfe bdry hbound hvol hdens hr

/--
[bc12_origin_openIncidence_of_trifurcation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc12core.lean)
-/
@[path]
private lemma bc12_origin_openIncidence_of_trifurcation_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {W : Finset (Sym2 (Site d))}
-- given
  (htri : IsCanonicalTrifurcation d ω 0)
  (_hW0 : ∀ e ∈ W, (0 : Site d) ∉ e) :
-- imply
  ∃ a₁ a₂ a₃ : Site d, (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧ (a₁ ≠ 0 ∧ a₂ ≠ 0 ∧ a₃ ≠ 0) ∧ ((openSubgraph d (forceOpenFinset W ω)).Adj 0 a₁ ∧ (openSubgraph d (forceOpenFinset W ω)).Adj 0 a₂ ∧ (openSubgraph d (forceOpenFinset W ω)).Adj 0 a₃) ∧ ((cluster d (removeSite 0 ω) a₁).Infinite ∧ (cluster d (removeSite 0 ω) a₂).Infinite ∧ (cluster d (removeSite 0 ω) a₃).Infinite) ∧ (cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₂ ∧ cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₃ ∧ cluster d (removeSite 0 ω) a₂ ≠ cluster d (removeSite 0 ω) a₃) := by
-- proof
  apply StatMech.Walls.bc12_origin_openIncidence_of_trifurcation ω htri W _hW0

/--
[bc12_isolated_origin_not_trifurcation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc12core.lean)
-/
@[path]
private lemma bc12_isolated_origin_not_trifurcation_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hiso : ∀ v : Site d, ¬ (openSubgraph d ω).Adj 0 v) :
-- imply
  ¬ IsCanonicalTrifurcation d ω 0 := by
-- proof
  apply StatMech.Walls.bc12_isolated_origin_not_trifurcation ω hiso

/--
[bc12_boxOriginTrifurcation_perOmega_of_canonical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc12core.lean)
-/
@[path]
private lemma bc12_boxOriginTrifurcation_perOmega_of_canonical_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (htri : IsCanonicalTrifurcation d ω 0) :
-- imply
  IsCanonicalTrifurcation d ω 0 ∧ ∃ W : Finset (Sym2 (Site d)), (∀ e ∈ W, (0 : Site d) ∉ e) ∧ ∃ y₁ y₂ y₃ : Site d, y₁ ≠ 0 ∧ y₂ ≠ 0 ∧ y₃ ≠ 0 ∧ Connected d (forceOpenFinset W ω) 0 y₁ ∧ Connected d (forceOpenFinset W ω) 0 y₂ ∧ Connected d (forceOpenFinset W ω) 0 y₃ ∧ (cluster d (removeSite 0 (forceOpenFinset W ω)) y₁).Infinite ∧ (cluster d (removeSite 0 (forceOpenFinset W ω)) y₂).Infinite ∧ (cluster d (removeSite 0 (forceOpenFinset W ω)) y₃).Infinite ∧ cluster d (removeSite 0 (forceOpenFinset W ω)) y₁ ≠ cluster d (removeSite 0 (forceOpenFinset W ω)) y₂ ∧ cluster d (removeSite 0 (forceOpenFinset W ω)) y₁ ≠ cluster d (removeSite 0 (forceOpenFinset W ω)) y₃ ∧ cluster d (removeSite 0 (forceOpenFinset W ω)) y₂ ≠ cluster d (removeSite 0 (forceOpenFinset W ω)) y₃ := by
-- proof
  apply StatMech.Walls.bc12_boxOriginTrifurcation_perOmega_of_canonical ω htri


-- created on 2026-10-23
