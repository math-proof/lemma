import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bc9core
open Set SimpleGraph StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech.Percolation.DisjointPaths MeasureTheory StatMech StatMech.Walls


/--
[bc9_originRewiring_of_boxOriginReach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc9core.lean)
-/
@[path]
private lemma bc9_originRewiring_of_boxOriginReach_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : bc9_BoxOriginReach d n) :
-- imply
  bc8_OriginRewiring d n := by
-- proof
  apply StatMech.Walls.bc9_originRewiring_of_boxOriginReach n h

/--
[bc9_canonicalTrif_of_boxOriginReach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc9core.lean)
-/
@[path]
private lemma bc9_canonicalTrif_of_boxOriginReach_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : bc9_BoxOriginReach d n)
  (hω : ω ∈ threeMeetBox d n) :
-- imply
  ∃ W : Finset (Sym2 (Site d)), (∀ e ∈ W, (0 : Site d) ∉ e) ∧ IsCanonicalTrifurcation d (forceOpenFinset W ω) 0 := by
-- proof
  apply StatMech.Walls.bc9_canonicalTrif_of_boxOriginReach n h ω hω

/--
[bc9_burtonKeane_uniqueness_of_boxOriginReach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc9core.lean)
-/
@[path]
private lemma bc9_burtonKeane_uniqueness_of_boxOriginReach_eq
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
  (hr : ∀ n : ℕ, bc9_BoxOriginReach d n) :
-- imply
  (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1) ∧ μ (atLeastTwoInfinite d) = 0 ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc9_burtonKeane_uniqueness_of_boxOriginReach μ herg hfe bdry hbound hvol hdens hr

/--
[bc9_forceOpenFinset_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc9core.lean)
-/
@[path]
private lemma bc9_forceOpenFinset_empty_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  forceOpenFinset (∅ : Finset (Sym2 (Site d))) ω = ω := by
-- proof
  apply StatMech.Walls.bc9_forceOpenFinset_empty ω

/--
[bc9_boxOriginReach_of_reach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc9core.lean)
-/
@[path]
private lemma bc9_boxOriginReach_of_reach_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {y₁ y₂ y₃ : Site d}
-- given
  (hy1 : y₁ ≠ 0)
  (hy2 : y₂ ≠ 0)
  (hy3 : y₃ ≠ 0)
  (hc1 : Connected d ω 0 y₁)
  (hc2 : Connected d ω 0 y₂)
  (hc3 : Connected d ω 0 y₃)
  (hi1 : (cluster d (removeSite 0 ω) y₁).Infinite)
  (hi2 : (cluster d (removeSite 0 ω) y₂).Infinite)
  (hi3 : (cluster d (removeSite 0 ω) y₃).Infinite)
  (hd12 : cluster d (removeSite 0 ω) y₁ ≠ cluster d (removeSite 0 ω) y₂)
  (hd13 : cluster d (removeSite 0 ω) y₁ ≠ cluster d (removeSite 0 ω) y₃)
  (hd23 : cluster d (removeSite 0 ω) y₂ ≠ cluster d (removeSite 0 ω) y₃) :
-- imply
  ∃ W : Finset (Sym2 (Site d)), (∀ e ∈ W, (0 : Site d) ∉ e) ∧ ∃ z₁ z₂ z₃ : Site d, z₁ ≠ 0 ∧ z₂ ≠ 0 ∧ z₃ ≠ 0 ∧ Connected d (forceOpenFinset W ω) 0 z₁ ∧ Connected d (forceOpenFinset W ω) 0 z₂ ∧ Connected d (forceOpenFinset W ω) 0 z₃ ∧ (cluster d (removeSite 0 (forceOpenFinset W ω)) z₁).Infinite ∧ (cluster d (removeSite 0 (forceOpenFinset W ω)) z₂).Infinite ∧ (cluster d (removeSite 0 (forceOpenFinset W ω)) z₃).Infinite ∧ cluster d (removeSite 0 (forceOpenFinset W ω)) z₁ ≠ cluster d (removeSite 0 (forceOpenFinset W ω)) z₂ ∧ cluster d (removeSite 0 (forceOpenFinset W ω)) z₁ ≠ cluster d (removeSite 0 (forceOpenFinset W ω)) z₃ ∧ cluster d (removeSite 0 (forceOpenFinset W ω)) z₂ ≠ cluster d (removeSite 0 (forceOpenFinset W ω)) z₃ := by
-- proof
  apply StatMech.Walls.bc9_boxOriginReach_of_reach ω hy1 hy2 hy3 hc1 hc2 hc3 hi1 hi2 hi3 hd12 hd13 hd23

/--
[bc9_originRewiring_iff_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc9core.lean)
-/
@[path]
private lemma bc9_originRewiring_iff_residue_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  bc9_BoxOriginReach d n → bc8_OriginRewiring d n := by
-- proof
  apply StatMech.Walls.bc9_originRewiring_iff_residue n


-- created on 2026-10-23
